from protocheck import logic
from protocheck.precedence import *
from protocheck.bspl_parser import BsplParser
from functools import partial
import itertools
import configargparse
import re
import pprint
import json
import textwrap
pp = pprint.PrettyPrinter()

def flatten(nested):
    return list(itertools.chain.from_iterable(nested))

class Specification():
    def __init__(self, protocols):
        self.protocols = {}
        self.references = {}
        self.type = 'specification'
        for p in protocols:
            proto = Protocol(p, self)
            self.protocols[proto.name] = proto
        for p in self.protocols.values():
            if p not in self.references:
                self.references[p] = set()
            for r in p.references:
                if r.type != 'protocol': continue
                if r.name in self.protocols:
                    self.references[p].add(self.protocols[r.name])
                else:
                    raise Exception("Reference to unknown protocol: " + r.name)
        for p in self.protocols.values():
            p.resolve_references(self)

def load(definition):
    parser = BsplParser(parseinfo=False)
    protocols = parser.parse(definition, rule_name='document')
    return Specification(protocols)

class Base():
    """Class containing elements common to protocols, messages, etc."""

    def __init__(self, schema, parent):
        self.schema = schema
        self.parent = parent

    @property
    def name(self):
        return self.schema['name']

    @property
    def type(self):
        return self.schema['type']

class Reference(Base):
    pass

def reference(schema, parent):
    if schema["type"] == "message":
        return Message(schema, parent)
    elif schema["type"] == "protocol":
        return Reference(schema, parent)
    else:
        raise Exception("Unknown type: " + schema["type"])

class Protocol(Base):
    def __init__(self, schema, parent=None):
        super().__init__(schema, parent)

        self.parameters = {p['name']: Parameter(p, self) for p in schema['parameters']}
        self.keys = {p for p in self.parameters.values() \
                     if p.key or parent.type=='protocol' and p.name in parent.parameters and parent.parameters[p.name].key}
        self.roles = {r['name']: Role(r, self) for r in schema.get('roles', [])}
        self.references = [reference(r, self) for r in schema.get('references', [])]

    def resolve_references(self, spec):
        self.references = [spec.protocols.get(r.name) or r for r in self.references]

    @property
    def all_parameters(self):
        return flatten([m.parameters.values() for m in self.messages.values()])

    def _adorned(self, adornment):
        "helper method for selecting parameters with a particular adornment"
        return {p for p in self.parameters.values() if p.adornment == adornment}

    @property
    def ins(self):
        return self._adorned('in')

    @property
    def outs(self):
        return self._adorned('out')

    @property
    def nils(self):
        return self._adorned('nil')

    @property
    def messages(self):
        return {k:v for r in self.references for k,v in r.messages.items()}

    def is_enactable(self):
        return consistent(logic.And(self.correct, self.enactable)).sat()[0]
            
    def is_live(self):
        return self.is_enactable() and not consistent(self.dead_end).sat()[0]
    
    def is_safe(self):
        #prove there are no unsafe enactments
        return not consistent(self.unsafe).sat()[0]

    def check_atomicity(self):
        for r in self.references:
            if isinstance(r, Message):
                continue
            else:
                expr = consistent(logic.And(self.correct,
                                      self.maximal,
                                      r.begin,
                                      r.incomplete))
                s = expr.sat()[1]
                if s:
                    return s
        return None

    def is_atomic(self):
        return not self.check_atomicity()

    def cover(self, parameter):
        if type(parameter) is not str: parameter = parameter.name
        alts = []
        for m in self.messages.values():
            if parameter in m.parameters and m.parameters[parameter].adornment == 'out':
                alts.append(m)
        return alts

    @property
    @logic.named
    def unsafe(self):
        clauses = []
        for p in self.all_parameters:
            if len(self.cover(p.name)) > 1:
                alts = []
                for r in self.roles.values():
                    #we assume that an agent can choose between alternative messages
                    alts.append(or_(*[m.sent for m in self.cover(p) if m.sender == r]))
                #at most one message producing this parameter can be observed at once
                #negate to prove it is impossible to break
                clauses.append(logic.Name(~onehot0(*alts), p.name + "-cover"))
        if clauses:
            #at least one conflict
            return logic.And(self.correct, *clauses)
        else:
            #no conflicting pairs; automatically safe -> not unsafe
            return bx.ZERO

    @property
    @logic.named
    def enactable(self):
        "It must be possible to bind each out parameter with at least one message"
        clauses = []
        for p in self.outs:
            clauses.append(or_(*[m.sent for m in self.cover(p)]))
        return and_(*clauses)

    @property
    @logic.named
    def dead_end(self):
        return logic.And(self.correct, self.maximal, self.incomplete)
    
    @property
    @logic.named
    def correct(self):
        clauses = []
        for m in self.messages.values():
            clauses.append(logic.And(m.emission, m.reception, m.transmission))
        for r in self.roles.values():
            clauses.append(logic.And(r.nonsimultaneity(self), r.minimality(self)))
        return logic.And(*clauses)

    @property
    @logic.named
    def maximal(self):
        "Each message must be sent, or it must be blocked by a prior binding"
        clauses = []
        for m in self.messages.values():
            clauses.append(m.sent | m.blocked)
        return and_(*clauses)

    @property
    @logic.named
    def begin(self):
        return or_(*[m.sent for m in self.messages.values()])

    def _complete(self):
        "Each out parameter must be observed by at least one role"
        clauses = []
        for p in self.outs:
            clauses.append(or_(*[m.received for m in self.cover(p)]))
        return and_(*clauses)

    @property
    @logic.named
    def complete(self):
        return self._complete()

    @property
    @logic.named
    def incomplete(self):
        return ~self._complete()

class Message(Protocol):
    def __init__(self, schema, parent):
        super().__init__(schema, parent)
        self.sender = parent.roles.get(schema['sender'])
        self.recipient = parent.roles.get(schema['recipient'])

    @property
    def messages(self):
        return {self.name: self}

    @property
    def sent(self):
        return send(self.sender, self.name)

    @property
    def received(self):
        return recv(self.recipient, self.name)

    @property
    def blocked(self):
        s = partial(observe, self.sender)
        nils = [and_(s(p), ~(sequential(s(p), self.sent) | simultaneous(s(p), self.sent))) for p in self.nils]
        outs = [s(p) for p in self.outs]
        return or_(*(nils + outs))

    @property
    @logic.named
    def transmission(self):
        "Each message emission corresponds exactly to a reception"
        return and_(eq(self.sent, self.received),
                    impl(self.sent, sequential(self.sent, self.received)))

    @property
    @logic.named
    def emission(self):
        """Sending a message must be preceded by observation of its ins,
           but cannot be preceded by observation of any nils or outs"""
        s = partial(observe, self.sender)
        ins = [impl(self.sent, sequential(s(p), self.sent))
               for p in self.ins]
        nils = [impl(and_(self.sent, s(p)), sequential(self.sent, s(p)))
                for p in self.nils]
        outs = [impl(self.sent, simultaneous(s(p), self.sent))
                for p in self.outs]
        return and_s(*(ins + nils + outs))

    @property
    @logic.named
    def reception(self):
        "Each message reception is accompanied by the observation of its parameters; either they are observed, or the message itself is not"
        clauses = [impl(self.received,
                        or_(sequential(p, self.received),
                            simultaneous(p, self.received)))
                   for p in map(partial(observe, self.recipient), self.ins)]
        clauses.extend([impl(self.received, simultaneous(p, self.received))
                        for p in map(partial(observe, self.recipient), self.outs)])
        return and_(*clauses)

class Role(Base):
    def messages(self, protocol):
        return {m.name:m for m in protocol.messages.values()
                if m.sender == self or m.recipient == self}

    def observe(self, msg):
        return observe(self.name, msg)

    def sent_messages(self, protocol):
        return [m for m in protocol.messages.values() if m.sender == self]

    @logic.named
    def minimality(self, protocol):
        "Every parameter observed by a role must have a corresponding message transmission or reception"
        sources = {}
        def add(m, p):
            if p in sources:
                sources[p].append(m)
            else:
                sources[p] = [m]

        for m in self.messages(protocol).values():
            if m.recipient == self:
                for p in m.ins:
                    add(m, p)
            for p in m.outs:
                add(m, p)

        return and_(*[impl(self.observe(p),
                           or_(*[self.observe(m) for m in sources[p]]))
                     for p in sources])

    @logic.named
    def nonsimultaneity(self, protocol):
        msgs = [m.sent for m in protocol.messages.values() if m.sender == self]
        if len(msgs) > 1:
            return ordered(*msgs)
        else:
            return bx.ONE

class Parameter(Base):
    def __init__(self, schema, parent=None):
        super().__init__(schema, parent)
        self.key = schema['key']

    @property
    def adornment(self):
        return self.schema['adornment']

@wrap(name)
def observe(role, event):
    return var(role + ":" + event)

send = observe
recv = observe

def strip_latex(spec):
    """Remove all instances of '\mapsto' and '\msf{}' from a latex listing, to make it proper BSPL"""
    spec = re.sub(r'\$\\msf{(\w+)}\$', r'\1', spec)
    spec = re.sub(r'\$\\mapsto\$', r'->', spec)
    return spec

if __name__ == "__main__":
    parser = configargparse.get_argument_parser()
    parser.description = 'BSPL Protocol property checker'
    parser.add('-i','--input', help='Input file name', required=True)
    parser.add('-p','--print-protocol', action="store_true",
               help='Print protocol specification')
    parser.add('-e','--print-enactability', action="store_true",
               help='Print enactment that satisfies enactability')
    args = parser.parse()

    with open(args.input) as file:
        raw = file.read()
        raw = strip_latex(raw)

        spec = load(raw)

        if args.print_protocol:
            print(raw)

        for protocol in spec.protocols.values():
            print("\n%s (%s): " % (protocol.name, args.input))

            if args.print_enactability:
                print(json.dumps(logic.And(protocol.correct, protocol.enactable), default=str, sort_keys=True, indent=2))
            e = protocol.is_enactable()
            print("  Enactable: ", e)
            if not e:
                print("    Formula:")
                print(json.dumps(logic.And(protocol.correct, protocol.enactable), default=str, sort_keys=True, indent=2))
                print()
            elif args.print_enactability:
                pp.pprint([k for k,v in consistent(logic.And(protocol.correct, protocol.enactable)).sat()[1].items() if v])

            l = protocol.is_live()
            print("  Live: ", l)
            if e and not l:
                print("    Formula:")
                print(json.dumps(protocol.dead_end, default=str, sort_keys=True, indent=2))
                print("\n    Violation:")
                pp.pprint([k for k,v in consistent(protocol.dead_end).sat()[1].items() if v])
                print()

            expr = protocol.unsafe
            us = consistent(expr).sat()[1]
            print("  Safe: ", not us)
            if us:
                print("\nFormula:")
                print(json.dumps(expr))
                print("\nViolation:")
                pp.pprint([k for k,v in us.items() if v])
                print()

            a = protocol.check_atomicity()
            print("  Atomic: ", not a)
            if a:
                print("\nViolation:")
                pp.pprint([k for k,v in a.items() if v])
                print()

        if not spec.protocols:
            print("No protocols parsed from file: ", args.input)
