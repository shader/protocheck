from protocheck import __version__, logic
from protocheck.precedence import consistent, pairwise,     \
    and_, or_, bx, sequential, simultaneous, impl, ordered, \
    reset_stats, stats, wrap, var, name
from protocheck.bspl_parser import BsplParser
from protocheck.logic import merge
from functools import partial
from more_itertools import intersperse
import itertools
import re
import pprint
import json
import grako
import sys
pp = pprint.PrettyPrinter()
debug = False


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
                if r.type != 'protocol':
                    continue
                if r.name in self.protocols:
                    self.references[p].add(self.protocols[r.name])
                else:
                    raise Exception("Reference to unknown protocol: " + r.name)
        for p in self.protocols.values():
            p.resolve_references(self)

    @property
    def roles(self):
        return set(r for r in p.roles for p in self.protocols.values())


def load(definition, path):
    parser = BsplParser(parseinfo=False)
    try:
        protocols = parser.parse(definition, rule_name='document')
        return Specification(protocols)
    except:  # catch *all* exceptions
        if not debug:  # suppress traceback by default
            e = sys.exc_info()[1]
            print("Error in: ", path, file=sys.stderr)
            print(e, file=sys.stderr)
            sys.exit(1)
        else:
            raise


def load_file(path):
    with open(path, 'r', encoding='utf8') as file:
        raw = file.read()
        raw = strip_latex(raw)

        spec = load(raw, path)
        return spec


class Base():
    """Class containing elements common to protocols, messages, etc."""

    def __init__(self, schema, parent):
        if isinstance(schema, grako.ast.AST):
            self.schema = schema.asjson()
        else:
            self.schema = schema.copy()
        self.parent = parent

    @property
    def name(self):
        return self.schema['name'].strip()

    @property
    def type(self):
        return self.schema['type']


class Reference(Base):
    def format(self, ref=True):
        parameters = self.schema.get('parameters') or self.schema.get('params')
        return "{}({}, {})".format(self.name,
                                   ", ".join([r['name']
                                              for r in self.schema['roles']]),
                                   ", ".join([Parameter(p).format() for p in parameters]))


def reference(schema, parent):
    if schema["type"] == "message":
        return Message(schema, parent)
    elif schema["type"] == "protocol":
        return Reference(schema, parent)
    else:
        raise Exception("Unknown type: " + schema["type"])


def atomic(p):
    c = p.correct
    m = p.maximal

    def inner(q, r):
        formula = logic.And(c, m,
                            r.enactability,
                            q.incomplete)
        return formula
    return inner


class Protocol(Base):
    def __init__(self, schema, parent=None):
        super().__init__(schema, parent)

        self.enactable = None

        self.public_parameters = {p['name']: Parameter(p, self)
                                  for p in schema['parameters']}
        self.private_parameters = {p['name']: Parameter(p, self)
                                   for p in schema.get('private') or []}
        self.keys = {p for p in self.parameters.values()
                     if p.key
                     or parent.type == 'protocol'
                     and p.name in parent.parameters
                     and parent.parameters[p.name].key}
        self.roles = {r['name']: Role(r, self)
                      for r in schema.get('roles', [])}
        self.references = [reference(r, self)
                           for r in schema.get('references', [])]

    def resolve_references(self, spec):
        refs = []
        for r in self.references:
            protocol = spec.protocols.get(r.name)
            if protocol:
                refs.append(protocol.instance(spec, self, r.schema))
            else:
                refs.append(r.instance(self))
        self.references = refs

    def instance(self, spec, parent, schema):
        p = Protocol(self.schema, parent)
        for i, r in enumerate(self.roles.values()):
            p.roles[r.name] = parent.roles.get(schema['params'][i]['name'])
        for i, par in enumerate(self.schema["parameters"]):
            p.public_parameters[par['name']].schema["name"] = \
                schema['params'][i + len(self.roles)]['name']
        p.resolve_references(spec)
        return p

    @property
    def parameters(self):
        return merge(self.public_parameters, self.private_parameters)

    def _adorned(self, adornment):
        "helper method for selecting parameters with a particular adornment"
        return {p.name for p in self.public_parameters.values()
                if p.adornment == adornment}

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
        return {k: v for r in self.references for k, v in r.messages.items()}

    def is_enactable(self):
        if self.enactable is None:
            self.enactable = consistent(
                logic.And(self.correct, self.enactability))
        return self.enactable

    def is_live(self):
        return self.is_enactable() and not consistent(self.dead_end)

    def is_safe(self):
        # prove there are no unsafe enactments
        return not consistent(self.unsafe)

    def recursive_property(self, prop, filter=None, verbose=None):
        for r in self.references:
            if filter and not filter(r):
                continue  # skip references that do not pass the filter
            formula = prop(self, r)
            if verbose:
                print_formula(formula)
            s = consistent(formula)
            if s:
                # found solution; short circuit
                return s, formula
            else:
                # recurse
                s, formula = r.recursive_property(prop, filter)
                if s:
                    return s, formula

        return None, None

    def check_atomicity(self, args=None):
        def filter(ref):
            return type(ref) is not Message or ref.is_entrypoint

        # if args and args.exhaustive:
        #     return self.recursive_property(atomic(self))
        # else:
        return self.recursive_property(atomic(self), filter, verbose=args and args.verbose)

    def is_atomic(self):
        solution, _ = self.check_atomicity()
        return not solution

    def p_cover(self, parameter):
        if type(parameter) is not str:
            parameter = parameter.name

        alts = []
        for m in self.messages.values():
            if parameter in m.parameters:
                alts.append(m)
        return alts

    @property
    @logic.named
    def cover(self):
        return logic.And(*[logic.Name(or_(*[m.received for m in self.p_cover(p)]),
                                      p.name + "-cover")
                           for p in self.public_parameters.values()])

    @property
    @logic.named
    def unsafe(self):
        clauses = []
        for p in self.public_parameters:
            # only public out parameters can have safety conflicts
            sources = [m for m in self.p_cover(p)
                       if m.parameters[p].adornment == 'out']
            if len(sources) > 1:
                alts = []
                for r in self.roles.values():
                    # assume an agent can choose between alternative messages
                    msgs = [m.sent for m in sources if m.sender == r]
                    if msgs:
                        alts.append(or_(*msgs))
                # at most one message producing this parameter can be sent
                more_than_one = or_(*pairwise(and_, alts))

                # only consider cases where more than one at once is possible
                if more_than_one:
                    clauses.append(
                        logic.Name(more_than_one, p + "-unsafe"))
        if clauses:
            # at least one conflict
            return logic.And(self.correct, logic.Name(clauses, "unsafe"))
        else:
            # no conflicting pairs; automatically safe -> not unsafe
            return bx.ZERO

    def _enactable(self):
        "Some message must be received containing each parameter"
        clauses = []
        for p in self.public_parameters:
            clauses.append(or_(*[m.received for m in self.p_cover(p)]))
        return and_(*clauses)

    @property
    @logic.named
    def enactability(self):
        return self._enactable()

    @property
    @logic.named
    def unenactable(self):
        return ~self._enactable()

    @property
    @logic.named
    def dead_end(self):
        return logic.And(self.correct, self.maximal, self.incomplete)

    @property
    @logic.named
    def correct(self):
        clauses = {}
        msgs = self.messages.values()
        roles = self.roles.values()
        clauses["Emission"] = {m.shortname: m.emission for m in msgs}
        clauses["Reception"] = {m.shortname: m.reception for m in msgs}
        clauses["Transmission"] = {m.shortname: m.transmission for m in msgs}
        clauses["Non-lossy"] = {m.shortname: m.non_lossy for m in msgs}
        clauses["Non-simultaneity"] = {r.name: r.nonsimultaneity(self)
                                       for r in roles}
        clauses["Minimality"] = {r.name: r.minimality(self) for r in roles}
        return clauses

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
            clauses.append(or_(*[m.received for m in self.p_cover(p)
                                 if m.parameters[p].adornment is 'out']))
        return and_(*clauses)

    @property
    @logic.named
    def complete(self):
        return self._complete()

    @property
    @logic.named
    def incomplete(self):
        return ~self._complete()

    @property
    def is_entrypoint(self):
        "A protocol is an entry point if it does not have any \
        dependencies on sibling protocols"
        return not self.ins - self.parent.ins

    def format(self, ref=False):
        if ref:
            return "{}({}, {})".format(self.name,
                                       ", ".join(self.roles),
                                       ", ".join([p.format() for p in self.public_parameters.values()]))
        else:
            return """{} {{
  roles {}
  parameters {}
{}
  {}
}}""".format(self.name,
             ", ".join(self.roles.keys()),
             ", ".join([p.format() for p in self.public_parameters.values()]),
             "  private " +
             ", ".join([p for p in self.private_parameters]) +
             "\n" if self.private_parameters else "",
             "\n  ".join([r.format(ref=True) for r in self.references]))

    def projection(protocol, role):
        schema = protocol.schema
        references = [
            r for r in protocol.references if role in r.roles.values()
            or r.type == 'message' and (role == r.sender or role == r.recipient)]

        messages = [m for m in references if m.type == 'message']

        if len(messages) > 0:
            projection = {
                'name': protocol.name,
                'type': 'protocol',
                'parameters': [p for p in schema['parameters']
                               if any(p['name'] in m.parameters for m in messages)],
                'private': [p for p in schema.get('private') or []
                            if any(p['name'] in m.parameters for m in messages)],
                'roles': [r for r in schema['roles']
                          if any(m.sender.name == r['name']
                                 or m.recipient.name == r['name']
                                 for m in messages)],
                'references': [r.schema for r in references],
            }
            return Protocol(projection, protocol.parent)


class Message(Protocol):
    def __init__(self, schema, parent):
        super().__init__(schema, parent)
        self.idx = 1

        self.sender = parent.roles.get(schema['sender'])
        if not self.sender:
            raise LookupError("Role not found", schema['sender'])
        self.recipient = parent.roles.get(schema['recipient'])
        if not self.recipient:
            raise LookupError("Role not found", schema['recipient'])

        for p in self.parameters:
            if p not in parent.parameters:
                raise LookupError("Undeclared parameter", p)

    @property
    def name(self):
        return self.parent.name + "/" + self.shortname

    @property
    def shortname(self):
        return self.schema['name'] + (str(self.idx) if self.idx > 1 else "")

    def instance(self, parent):
        msg = Message(self.schema, parent)

        # handle duplicates
        for m in parent.references:
            if m == self:
                break
            if m.schema['name'] == self.schema['name']:
                msg.idx += 1

        # propagate renaming from parent protocol
        for i, par in enumerate(self.public_parameters.values()):
            msg.public_parameters[par.name].schema["name"] = \
                parent.parameters[par.name].name

        return msg

    @property
    def messages(self):
        return {self.shortname: self}

    @property
    def sent(self):
        return send(self.sender, self.name)

    @property
    def received(self):
        return recv(self.recipient, self.name)

    @property
    @logic.named
    def enactability(self):
        return self.received

    def check_atomicity(self):
        return None, None

    @property
    @logic.named
    def unenactable(self):
        return ~self.received

    @property
    def blocked(self):
        s = partial(observe, self.sender)
        ins = [~s(p) for p in self.ins]
        nils = [and_(s(p), ~(sequential(s(p), self.sent) |
                             simultaneous(s(p), self.sent))) for p in self.nils]
        outs = [s(p) for p in self.outs]
        return or_(*(nils + outs + ins))

    @property
    def transmission(self):
        "Each message reception is causally preceded by its emission"
        return impl(self.received, sequential(self.sent, self.received))

    @property
    def non_lossy(self):
        "Each message emission results in reception"
        return impl(self.sent, self.received)

    @property
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
        return and_(*(ins + nils + outs))

    @property
    def reception(self):
        "Each message reception is accompanied by the observation of its parameters; either they are observed, or the message itself is not"
        clauses = [impl(self.received,
                        or_(sequential(p, self.received),
                            simultaneous(p, self.received)))
                   for p in map(partial(observe, self.recipient), self.ins | self.outs)]
        return and_(*clauses)

    def format(self, ref=False):
        return "{} -> {}: {}[{}]".format(self.sender.name,
                                         self.recipient.name,
                                         self.shortname,
                                         ', '.join([p.format() for p in self.parameters.values()]))


class Role(Base):
    def messages(self, protocol):
        return {m.name: m for m in protocol.messages.values()
                if m.sender == self or m.recipient == self}

    def observe(self, msg):
        return observe(self.name, msg)

    def sent_messages(self, protocol):
        return [m for m in protocol.messages.values() if m.sender == self]

    def minimality(self, protocol):
        """Every parameter observed by a role must have a corresponding
        message transmission or reception"""
        sources = {}

        def add(m, p):
            if p in sources:
                sources[p].append(m)
            else:
                sources[p] = [m]

        outgoing = set()
        for m in self.messages(protocol).values():
            if m.recipient == self:
                for p in m.ins.union(m.outs):
                    add(m, p)
            else:
                for p in m.outs:
                    add(m, p)
                for p in m.ins:
                    outgoing.add(p)

        # keep track of 'in' parameters being sent without sources
        # unsourced parameters cannot be observed
        unsourced = [logic.Name(~self.observe(p), p)
                     for p in outgoing - set(sources.keys())]

        # sourced parameters must be received or sent to be observed
        sourced = [logic.Name(impl(self.observe(p),
                                   or_(*[simultaneous(self.observe(m), self.observe(p))
                                         for m in sources[p]])),
                              p)
                   for p in sources]

        return logic.And(*(unsourced + sourced))

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

    def format(self):
        base = "{} {}".format(self.adornment, self.name)
        if self.key:
            return base + " key"
        else:
            return base


@wrap(name)
def observe(role, event):
    return var(role + ":" + event)


send = observe
recv = observe


def strip_latex(spec):
    """Remove all instances of '\\mapsto' and '\\msf{}' from a latex listing, to make it proper BSPL"""
    spec = re.sub(r'\$\\msf{(\w+)}\$', r'\1', spec)
    spec = re.sub(r'\$\\mapsto\$', r'->', spec)

    spec = re.sub(r'\$\\role\$', r'roles', spec)
    spec = re.sub(r'\$\\param\$', r'parameters', spec)
    spec = re.sub(r'\$\\mo\$', r'->', spec)
    return spec


def print_formula(*formulas):
    print("\nFormula:")
    print(json.dumps(logic.merge(*formulas),
                     default=str, sort_keys=True, indent=2))
    print()


def handle_enactability(protocol, args):
    reset_stats()
    e = protocol.is_enactable()
    print("  Enactable: ", bool(e))
    if args.verbose or args.stats:
        print("    stats: ", stats)
    if not e and not args.quiet or args.verbose:
        print_formula(logic.And(protocol.correct, protocol.enactability))
    if e and args.verbose:
        pp.pprint(e)

    return e


def handle_liveness(protocol, args):
    reset_stats()
    e = protocol.is_enactable()
    violation = consistent(protocol.dead_end)
    print("  Live: ", e and not violation)
    if args.verbose or args.stats:
        print("    stats: ", stats)
    if violation and not args.quiet or args.verbose:
        print_formula(protocol.dead_end)
    if violation and not args.quiet:
        print("\n    Violation:")
        pp.pprint(violation)
        print()


def handle_safety(protocol, args):
    reset_stats()
    expr = protocol.unsafe
    violation = consistent(expr)
    print("  Safe: ", not violation)
    if args.verbose or args.stats:
        print("    stats: ", stats)
    if violation and not args.quiet or args.verbose:
        print_formula(expr)
    if violation and not args.quiet:
        print("\nViolation:")
        pp.pprint(violation)
        print()


def handle_atomicity(protocol, args):
    reset_stats()
    a, formula = protocol.check_atomicity(args)
    print("  Atomic: ", not a)
    if args.verbose or args.stats:
        print("    stats: ", stats)
    if a and not args.quiet:
        print("\nViolation:")
        pp.pprint(a)
        print("\nFormula:")
        print(json.dumps(formula, default=str, sort_keys=True, indent=2))
        print()


def handle_projection(args):
    role_name = args.input[0]
    spec = load_file(args.input[1])

    projections = []
    for protocol in spec.protocols.values():
        schema = protocol.schema
        if args.verbose:
            print(schema)

        role = protocol.roles.get(role_name)
        if not role:
            raise LookupError("Role not found", role_name)

        projections.append(protocol.projection(role))

    for p in projections:
        print(p.format())
