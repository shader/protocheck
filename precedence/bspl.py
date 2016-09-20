from precedence.precedence import *
from precedence.bspl_parser import bsplParser
from functools import partial

messages = []
parameters = []

class Message():
    def __init__(self, schema, **kwargs):
        self.schema = schema
        self.protocol = kwargs.get('protocol', None)

        #Any parameters declared as keys in a protocol are keys in its messages
        if self.protocol:
            for p in self.parameters:
                if p['name'] in self.protocol.keys:
                    p['key'] = True

    @property
    def name(self):
        return self.schema['name']

    @property
    def parameters(self):
        return [p for p in self.schema['parameters']]

    @property
    def keys(self):
        protocol_keys = self.protocol.keys if self.protocol else []
        return [p['name'] for p in self.schema['parameters'] if p['key']]

    def _adorned(self, adornment):
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
    def sender(self):
        return self.schema['sender']

    @property
    def recipient(self):
        return self.schema['recipient']

class Role():
    def __init__(self, schema):
        self.schema = schema

    @property
    def name(self):
        return self.schema['name']

    @property
    def messages(self):
        return self.schema['messages']

class Protocol():
    def __init__(self, schema):
        self.schema = schema
        self._roles = {r['name']: Role(r) for r in schema['roles']}
        self._references = []

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
    def keys(self):
        return [p['name'] for p in self.schema['parameters'] if p['key']]

    @property
    def roles(self):
        return self._roles

    @property
    def references(self):
        return self._references

    @property
    def messages(self):
        return [r for r in self._references if r.type == "message"]

def reference(schema):
    if schema["type"] == "message":
        return Message(schema)
    elif schema["type"] == "protocol":
        return Protocol(schema)
    else:
        raise Exception("Unknown reference type: " + schema["type"])
    
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

def minimality(parameter, role):
    "Every parameter observed by a role must have a corresponding message transmission or reception"
    messages = [m for m in role.messages if paraameter in m.parameters]
    clauses = [Implies(observe(role, parameter), send(role, m) | recv(role, m)) for m in messages]
    return And(*clauses)

if name == "__main__":
    ast = generic_main(main, bsplParser, name='bspl')
    
