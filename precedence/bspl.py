from precedence.precedence import *
from precedence.bspl_parser import BsplParser
from functools import partial
import itertools

def flatten(nested):
    return list(itertools.chain.from_iterable(nested))


references = {}
def reference(schema, parent=None):
    #return any existing matching references
    name = schema['name']
    if not references.get(name, None):
        if schema["type"] == "message":
            references[name] = Message(schema, parent)
        elif schema["type"] == "protocol":
            references[name] = Protocol(schema, parent)
        else:
            raise Exception("Unknown reference type: " + schema["type"])
    return references[name]

def parse(definition):
    parser = BsplParser(parseinfo=False)
    return parser.parse(definition, rule_name='protocol')

class Protocol():
    def __init__(self, schema, parent=None):
        self.schema = schema
        self.parent = parent

        self.keys = [p['name'] for p in self.parameters if p['key']]
        if parent:
            self.keys += parent.keys

        self.references = [reference(r, self) for r in schema.get('references', [])]

        self.roles = {r['name']: Role(r, self) for r in schema.get('roles', [])}

    @classmethod
    def load(cls, definition):
        return cls(parse(definition))

    @property
    def name(self):
        return self.schema['name']

    @property
    def type(self):
        return self.schema['type']

    @property
    def parameters(self):
        return self.schema['parameters']

    @property
    def all_parameters(self):
        return flatten([m.parameters for m in self.messages])

    def _adorned(self, adornment):
        "helper method for selecting parameters with a particular adornment"
        return [m for m in self.parameters if m['adornment'] == adornment]

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

    def is_live(self):
        pass

    def is_safe(self):
        pass

    def is_atomic(self):
        pass

    def enactibility(self):
        pass

    def correctness(self):
        pass

    def maximality(self):
        pass

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

    @property
    def sender(self):
        return self.schema['sender']

    @property
    def recipient(self):
        return self.schema['recipient']

    @property
    def messages(self):
        return {self.name: self}

    def sent(self):
        return send(self.sender, self.name)

    def received(self):
        return send(self.recipient, self.name)

    def transmission(self):
        "A message must be sent before it can be received"
        return ~self.received() | sequential(self.sent(), self.received())

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

    def reception(self):
        "Each message reception is accompanied by the observation of its parameters; either they are observed, or the message itself is not"
        clauses = [Or(~self.received(),
                      sequential(p, self.received()),
                      simultaneous(p, self.received()))
               for p in map(partial(observe, recipient), self.ins + self.outs)]
        return And(*clauses)

class Role():
    def __init__(self, schema, parent):
        self.schema = schema
        self.parent = parent

    @property
    def name(self):
        return self.schema['name']

    @property
    def messages(self):
        return [m for m in parent.messages
                if m.sender == self.name or m.recipient == self.name]

    def observe(self, msg):
        return observe(self.name, msg)

    def minimality(self, parameter):
        "Every parameter observed by a role must have a corresponding message transmission or reception"
        msgs = [m for m in self.messages if parameter in m.ins or parameter in m.outs]
        clauses = [self.observe(m) for m in msgs]
        return Implies(self.observe(parameter), Or(*clauses))

    def ordering(self):
        return ordered(*[m for m in self.parent.messages if m.sender == self.name])

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
