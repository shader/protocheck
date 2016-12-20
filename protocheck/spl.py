from protocheck.precedence import *
from protocheck.spl_parser import SplParser
from functools import partial

messages = []
parameters = []

class Message():
    def __init__(self, schema):
        self.schema = schema

    @property
    def name(self):
        return self.schema['name']

    @property
    def data(self):
        return self.schema['data']

    @property
    def ins(self):
        return [m for m in self.data if m.adornment == 'in']

    @property
    def outs(self):
        return [m for m in self.data if m.adornment == 'out' or m.adornment == None]

    @property
    def keys(self):
        return self.schema['key']

    @property
    def parameters(self):
        return self.data + self.keys
    
    @property
    def sender(self):
        return self.schema['sender']

    @property
    def recipients(self):
        return self.schema['recipients']

class Role():
    def __init__(self, schema):
        self.schema = schema

    @property
    def name(self):
        return self.schema['name']

    @property
    def messages(self):
        return self.schema['messages']
    
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
    return and_(and_(*ins), *outs)
        
def reception(msg, recipient):
    "Each message reception is accompanied by the observation of its parameters; either they are observed, or the message itself is not"
    r = recv(recipient, msg)
    clauses = [or_(~r,
                  sequential(p, r),
                  simultaneous(p, r))
               for p in map(partial(observe, recipient), msg.parameters)]
    return and_(*clauses)

def minimality(parameter, role):
    "Every parameter observed by a role must have a corresponding message transmission or reception"
    messages = [m for m in role.messages if paraameter in m.parameters]
    clauses = [Implies(observe(role, parameter), send(role, m) | recv(role, m)) for m in messages]
    return and_(*clauses)

if name == "__main__":
    ast = generic_main(main, splParser, name='spl')
