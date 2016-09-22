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
            cls._registry[name] = super(Registered, cls).__call__(schema, *args, **kwargs)

        obj = cls._registry[name]
        obj.new_instance(schema, parent)
        return obj

class Base(metaclass=Registered):
    def __init__(self, schema, parent=None):
        self.schema = schema
        self.parent = parent

    @property
    def name(self):
        return self.schema['name']

    @property
    def type(self):
        return self.schema['type']

    def new_instance(self, schema, parent):
        pass

def reference(schema, parent=None):
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

        self.parameters = {Parameter(p, self) for p in schema['parameters']}
        
        self.keys = {p for p in self.parameters if p.key}
        if parent:
            self.keys.update(parent.keys)

        self.roles = {r['name']: Role(r, self) for r in schema.get('roles', [])}

        self.references = [reference(r, self) for r in schema.get('references', [])]

    @property
    def all_parameters(self):
        return flatten([m.parameters for m in self.messages])

    def _adorned(self, adornment):
        "helper method for selecting parameters with a particular adornment"
        return [p for p in self.parameters if p.adornment(self) == adornment]

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
        return consistent(And(self.correctness, self.enactability))
            
    def is_live(self):
        return self.is_enactable() and not consistent(And(self.correctness,
                                                          self.maximality,
                                                          ~self.completion))

    def is_safe(self):
        clauses = []
        for p in self.parameters:
            if len(p.messages['out']) > 1:
                #at most one message producing this parameter can be observed at once
                #negate to prove it is impossible to break
                clauses.extend(~OneHot0(*p.messages['out']))

        return not consistent(And(self.correctness, *clauses))

    def is_atomic(self):
        pass

    @property
    def enactability(self):
        pass

    @property
    def correctness(self):
        clauses = []
        for m in self.messages:
            clauses.push(And(m.transmission, m.emission, m.reception))
        for r in self.roles:
            clauses.push(And(r.ordering, r.minimality))
        return And(*clauses)

    @property
    def maximality(self):
        pass

    @property
    def completion(self):
        "Each out parameter must be observed by at least one role"
        clauses = []
        for p in self.outs:
            alts = []
            for role in roles:
                alts.push(observe(role, p))
            clauses.push(Or(*alts))
        return And(*clauses)

class Message(Protocol):
    def __init__(self, schema, parent=None):
        super().__init__(schema, parent)
        self.sender = Role({"name": schema['sender']}, parent)
        self.recipient = Role({"name": schema['recipient']}, parent)

    @property
    def messages(self):
        return {self.name: self}

    def sent(self):
        return send(self.sender, self.name)

    def received(self):
        return send(self.recipient, self.name)

    @property
    def transmission(self):
        "A message must be sent before it can be received"
        return ~self.received() | sequential(self.sent(), self.received())

    @property
    def emission(self):
        """Sending a message must be preceded by observation of its ins,
           but cannot be preceded by observation of any nils"""
        ins = [~self.sent() | sequential(observe(self.sender, p), self.sent())
               for p in self.ins]
        nils = [~self.sent() | ~sequential(observe(self.sender, p), self.sent())
                for p in self.nils]
        outs = [~self.sent() | simultaneous(observe(self.sender, p), self.sent())
                for p in self.outs]
        return And(And(And(*ins), *nils), *outs)

    @property
    def reception(self):
        "Each message reception is accompanied by the observation of its parameters; either they are observed, or the message itself is not"
        clauses = [Or(~self.received(),
                      sequential(p, self.received()),
                      simultaneous(p, self.received()))
               for p in map(partial(observe, recipient), self.ins + self.outs)]
        return And(*clauses)

class Role(Base):
    @property
    def messages(self):
        return [m for m in parent.messages
                if m.sender == self.name or m.recipient == self.name]

    def observe(self, msg):
        return observe(self.name, msg)

    def minimality(self):
        "Every parameter observed by a role must have a corresponding message transmission or reception"
        sources = {}
        for m in self.messages:
            if m.sender == self.name:
                for p in m.ins + m.outs:
                    if p in sources:
                        sources[p].push(m)
                    else:
                        sources[p] = [m]
        
        return And(*[Implies(self.observe(p),
                             Or(*[self.observe(m) for m in sources[p]]))
                     for p in sources])

    @property
    def ordering(self):
        return ordered(*[m for m in self.parent.messages if m.sender == self.name])

class Parameter(Base):
    def __init__(self, schema, parent=None):
        super().__init__(schema, parent)
        self.key = schema['key']
        self.messages = {}
        self.instances = {}

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
    return exprvar(role + ":" + event)

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
               for p in map(partial(observe, recipient), msg.parameters)]
    return And(*clauses)

if name == "__main__":
    ast = generic_main(main, bsplParser, name='bspl')
