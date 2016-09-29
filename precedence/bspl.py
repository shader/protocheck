from precedence.precedence import *
from precedence.bspl_parser import BsplParser
from functools import partial
import itertools

def flatten(nested):
    return list(itertools.chain.from_iterable(nested))

class Registered(type):
    _registry = {}
    def __call__(cls, schema, parent=None, *args, **kwargs):
        name = schema['name'] if isinstance(schema, dict) else schema

        if name not in cls._registry:
            cls._registry[name] = super(Registered, cls).__call__(schema, parent, *args, **kwargs)

        obj = cls._registry[name]
        obj.new_instance(schema, parent)
        return obj

class Base(metaclass=Registered):
    def __init__(self, schema, parent):
        self.schema = schema
        self.parent = parent

    @classmethod
    def reset_registry(cls):
        cls._registry = {}

    @property
    def name(self):
        return self.schema['name']

    @property
    def type(self):
        return self.schema['type']

    def new_instance(self, schema, parent):
        pass

def reference(schema, parent):
    if schema["type"] == "message":
        return Message(schema, parent)
    elif schema["type"] == "protocol":
        return Protocol(schema, parent)
    else:
        raise Exception("Unknown reference type: " + schema["type"])

def load(definition):
    parser = BsplParser(parseinfo=False)
    protocols = parser.parse(definition, rule_name='document')
    return [Protocol(p, None) for p in protocols]

class Protocol(Base):
    def __init__(self, schema, parent=None):
        super().__init__(schema, parent)

        self.parameters = {p['name']: Parameter(p, self) for p in schema['parameters']}
        
        self.keys = {p for p in self.parameters.values() if p.key}
        if parent:
            self.keys.update(parent.keys)

        self.roles = {r['name']: Role(r, self) for r in schema.get('roles', [])}

        self.references = [reference(r, self) for r in schema.get('references', [])]

    @property
    def all_parameters(self):
        return flatten([m.parameters.values() for m in self.messages])

    def _adorned(self, adornment):
        "helper method for selecting parameters with a particular adornment"
        return {p for p in self.parameters.values() if p.adornment(self) == adornment}

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
        return consistent(And(self.correct, self.enactable)).satisfy_one()
            
    def is_live(self):
        return self.is_enactable() and not consistent(self.dead_end).satisfy_one()

    def is_safe(self):
        #prove there are no unsafe enactments
        return not consistent(self.unsafe).satisfy_one()

    def is_atomic(self):
        for r in self.references:
            if isinstance(r, Message):
                continue
            elif not consistent(And(self.correct,
                                    self.maximal,
                                    r.begin,
                                    ~r.complete)).satisfy_one():
                return False
        return True

    @property
    def unsafe(self):
        clauses = []
        for p in self.parameters.values():
            if len(p.messages['out']) > 1:
                #at most one message producing this parameter can be observed at once
                #negate to prove it is impossible to break
                clauses.extend(~OneHot0(*p.messages['out']))
        if clauses:
            #at least one conflict
            return And(self.correct, *clauses)
        else:
            #no conflicting pairs; automatically safe
            return bx.ZERO


    @property
    def enactable(self):
        "It must be possible to bind each out parameter with at least one message"
        clauses = []
        for p in self.outs:
            clauses.append(Or(*[m.sent for m in p.messages['out']]))
        return And(*clauses)

    @property
    def dead_end(self):
        return And(self.correct, self.maximal, ~self.complete)

    @property
    def correct(self):
        clauses = []
        for m in self.messages.values():
            clauses.append(And(m.transmission, m.emission, m.reception))
        for r in self.roles.values():
            clauses.append(And(r.ordering, r.minimality))
        return And(*clauses)

    @property
    def maximal(self):
        "Each message must be sent, or it must be blocked by a prior binding"
        clauses = []
        for m in self.messages.values():
            clauses.append(m.delivered)
            clauses.append(m.sent | m.blocked)
        return And(*clauses)

    @property
    def begin(self):
        return Or(*[m.sent for m in self.messages.values()])

    @property
    def complete(self):
        "Each out parameter must be observed by at least one role"
        clauses = []
        for p in self.outs:
            alts = []
            for role in self.roles:
                alts.append(observe(role, p))
            clauses.append(Or(*alts))
        return And(*clauses)

class Message(Protocol):
    def __init__(self, schema, parent):
        super().__init__(schema, parent)
        self.sender = Role({"name": schema['sender']}, parent)
        self.recipient = Role({"name": schema['recipient']}, parent)

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
    def delivered(self):
        return Implies(self.sent, self.received)

    @property
    def blocked(self):
        return Or(*[observe(self.sender, p) for p in self.nils.union(self.outs)])

    @property
    def transmission(self):
        "A message must be sent before it can be received"
        return ~self.received | sequential(self.sent, self.received)

    @property
    def emission(self):
        """Sending a message must be preceded by observation of its ins,
           but cannot be preceded by observation of any nils"""
        ins = [~self.sent | sequential(observe(self.sender, p), self.sent)
               for p in self.ins]
        nils = [~self.sent | ~sequential(observe(self.sender, p), self.sent)
                for p in self.nils]
        outs = [~self.sent | simultaneous(observe(self.sender, p), self.sent)
                for p in self.outs]
        return And(And(And(*ins), *nils), *outs)

    @property
    def reception(self):
        "Each message reception is accompanied by the observation of its parameters; either they are observed, or the message itself is not"
        clauses = [Or(~self.received,
                      sequential(p, self.received),
                      simultaneous(p, self.received))
               for p in map(partial(observe, self.recipient), self.ins.union(self.outs))]
        return And(*clauses)

class Role(Base):
    @property
    def messages(self):
        return {m.name:m for m in self.parent.messages.values()
                if m.sender == self or m.recipient == self}

    def observe(self, msg):
        return observe(self.name, msg)

    @property
    def minimality(self):
        "Every parameter observed by a role must have a corresponding message transmission or reception"
        sources = {}
        for m in self.messages.values():
            if m.sender == self:
                for p in m.ins.union(m.outs):
                    if p in sources:
                        sources[p].append(m)
                    else:
                        sources[p] = [m]

        return And(*[Implies(self.observe(p),
                             Or(*[self.observe(m) for m in sources[p]]))
                     for p in sources])

    @property
    def ordering(self):
        msgs = [m.sent for m in self.parent.messages.values() if m.sender == self]
        if len(msgs) > 1:
            return ordered(*msgs)
        else:
            return bx.ONE

class Parameter(Base):
    def __init__(self, schema, parent=None):
        super().__init__(schema, parent)
        self.key = schema['key']
        self.instances = {}
        self.messages = {}

        self.new_instance(schema, parent)

    def new_instance(self, schema, parent):
        self.instances[parent] = schema

        if isinstance(parent, Message):
            a = schema['adornment']
            if a in self.messages:
                self.messages[a].add(parent)
            else:
                self.messages[a] = {parent}

    @property
    def sources(self):
        return self.messages.get('in', set()).union(self.messages.get('out', set()))

    def adornment(self, parent):
        return self.instances.get(parent, {}).get('adornment')

@wrap(name)
def observe(role, event):
    return var(role + ":" + event)

send = observe
recv = observe

def transmission(msg, sender, recipient):
    "A message must be sent before it can be received"
    return ~observe(recipient, msg) | sequential(observe(sender, msg), observe(recipient, msg))

def dependencies(msg, sender):
    "Sending a message must be preceded by observation of its ins, and occur simultaneous to observation of its outs"
    ins = [~send(sender, msg) | sequential(observe(sender, p), send(sender, msg)) for p in msg.ins]
    outs = [~send(sender, msg) | simultaneous(observe(sender, p), send(sender, msg)) for p in msg.outs]
    return And(And(*ins), *outs)
        
def reception(msg, recipient):
    "Each message reception is accompanied by the observation of its parameters; either they are observed, or the message itself is not"
    r = recv(recipient, msg)
    clauses = [Or(~r,
                  sequential(p, r),
                  simultaneous(p, r))
               for p in map(partial(observe, recipient), msg.parameters.values())]
    return And(*clauses)

if name == "__main__":
    ast = generic_main(main, bsplParser, name='bspl')
