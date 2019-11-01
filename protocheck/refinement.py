from protocheck.bspl import load_file, Message, Role
import sys


def handle_refinement(args):
    path = args.input[0]
    spec = load_file(path)
    Q = spec.protocols[args.input[1]]
    P = spec.protocols[args.input[2]]

    result = refines(UoD(), P.public_parameters.keys(),
                     Q, P, verbose=args.verbose)
    if result["ok"] == True:
        print("  {} Refines {}".format(Q.name, P.name))
        return True
    else:
        print(result)
        return False


def empty_path():
    """The empty path is a list with no message instances"""
    return tuple()


External = Role({'name': "*External*"}, None)


class Instance():
    def __init__(self, msg, delay=float('inf')):
        self.msg = msg
        self.delay = delay

    def __str__(self):
        return "<{},{}>".format(self.msg.name, self.delay)

    def __repr__(self):
        return str(self)

    def __eq__(self, other):
        if isinstance(other, self.__class__):
            return self.msg == other.msg and self.delay == other.delay
        else:
            return False

    def __hash__(self):
        return (self.msg, self.delay).__hash__()

    @property
    def received(self):
        return self.delay < float('inf')


def key_sets(path):
    keys = set()
    for i in path:
        keys.add(tuple(i.msg.keys))
    return keys


def known(path, keys, R):
    """Compute the set of parameters observed by role R after enacting path"""
    time = 0
    k = set()
    for instance in path:
        if (set(instance.msg.parameters) >= set(keys)
            and (instance.msg.sender.name == R.name
                 or (instance.msg.recipient.name == R.name
                     and instance.delay + time <= len(path)))):
            k.update(set(instance.msg.ins))
            k.update(set(instance.msg.outs))
        time += 1
    return k


def viable(path, msg):
    msg_count = len([i.msg for i in path if i.msg == msg])
    if not msg.ins.symmetric_difference({p.name for p in msg.parameters.values()}) and msg_count > 0:
        # only allow one copy of an all "in" message
        return False
    if msg.sender == External:
        k = known(path, (), msg.recipient)
        if not k.issuperset(msg.ins):
            return True
        else:
            return False
    k = known(path, msg.keys, msg.sender)
    return k.issuperset(msg.ins) \
        and k.isdisjoint(msg.outs) \
        and k.isdisjoint(msg.nils)


class UoD():
    def __init__(self, messages={}, roles={}):
        self.messages = set(messages)
        self.roles = set(roles)

    @staticmethod
    def from_protocol(protocol):
        if not protocol.ins.union(protocol.nils):
            return UoD(list(protocol.messages.values()), protocol.roles.values())
        else:
            dependencies = {}
            for r in protocol.roles.values():
                keys = protocol.ins.intersection(protocol.keys)
                # generate messages that provide p to each sender
                schema = {
                    'name': f'external->{r.name}',
                    'sender': External.name,
                    'recipient': r.name,
                    'parameters': [{'adornment': 'in', 'name': k, 'key': True} for k in keys]
                    + [{'adornment': 'in', 'name': p, 'key': False}
                        for p in protocol.ins.difference(keys)]
                }
                dependencies[r.name] = schema
            protocol.roles[External.name] = External
            uod = UoD(list(protocol.messages.values()) + [Message(s, protocol) for s in dependencies.values()],
                      protocol.roles.values())
            return uod

    def __add__(self, other):
        return UoD(self.messages.union(other.messages), self.roles.union(other.roles))


def branches(U, path):
    b = set()
    for msg in U.messages:
        # print(msg.name, viable(path, msg))
        if viable(path, msg):
            # default messages to unreceived, progressively receive them later
            inst = Instance(msg, float("inf"))
            if msg.sender == External:
                inst.delay = 0
            b.add(inst)
    return b


def unreceived(path):
    return set(i for i in path if i.delay == float("inf"))


def receive(path, instance):
    p = list(path)
    i = p.index(instance)
    p[i] = Instance(instance.msg, len(p) - i - 1)
    return tuple(p)


def extensions(U, path):
    xs = {path + (b,) for b in branches(U, path)}
    return xs.union({receive(path, u) for u in unreceived(path)})


def sources(path, p):
    """The set of all roles that produce p as an out parameter in path"""
    return set(i.msg.sender.name for i in path if p in i.msg.outs)


def subsumes(U, params, a, b, verbose=False):
    """Path a subsumes path b"""
    if verbose:
        print("path a: ", a)
        print("path b: ", b)
    for p in params:
        sources_a = sources(a, p)
        sources_b = sources(b, p)
        if sources_a != sources_b:
            if verbose:
                print("sources don't match: {} != {}".format(
                    sources_a, sources_b))
            return False

    for r in U.roles:
        for keys in key_sets(a):
            if verbose:
                print(keys)
            known_a = known(a, keys, r).intersection(params)
            known_b = known(b, keys, r).intersection(params)
            if known_a != known_b:
                if verbose:
                    print("{}'s knowledge doesn't match: {} != {}".format(
                        r.name, known_a, known_b))
                return False
            elif verbose:
                print("{} knows: {}".format(r.name, known_a))
    if len(b) > 1:
        b2 = b[:-1]
        return any(subsumes(U, params, a[:end], b2, verbose) for end in range(len(a)))
    else:
        return True


def max_paths(U):
    max_paths = []
    new_paths = [empty_path()]
    while len(new_paths):
        p = new_paths.pop()
        xs = extensions(U, p)
        if xs:
            new_paths.extend(xs)
        else:
            max_paths.insert(len(max_paths), p)
    return max_paths


def total_knowledge(U, path):
    k = set()
    for r in U.roles:
        for keys in key_sets(path):
            k.update(known(path, keys, r))
    return k


def path_liveness(protocol):
    U = UoD.from_protocol(protocol)
    new_paths = [empty_path()]
    while len(new_paths):
        p = new_paths.pop()
        xs = extensions(U, p)
        if xs:
            new_paths.extend(xs)
        else:
            if total_knowledge(U, p).intersection(protocol.outs) < protocol.outs:
                return {"live": False,
                        "reason": "Found path that does not extend to completion",
                        "path": p}
    return {"live": True}


def path_safety(protocol):
    U = UoD.from_protocol(protocol)
    parameters = {p for m in protocol.messages.values() for p in m.outs}
    new_paths = [empty_path()]
    while len(new_paths):
        path = new_paths.pop()
        xs = extensions(U, path)
        if xs:
            new_paths.extend(xs)
        for p in parameters:
            if len(sources(path, p)) > 1:
                return {"safe": False,
                        "reason": "Found parameter with multiple sources in a path",
                        "path": path,
                        "parameter": p}
    return {"safe": True}


def all_paths(U, verbose=False):
    paths = set()
    new_paths = {empty_path()}
    total_paths = 0
    longest_path = 0
    while new_paths:
        p = new_paths.pop()
        if len(p) > longest_path:
            longest_path = len(p)
        if len(p) > len(U.messages):
            print("Path too long: ", p)
            exit(1)
        xs = extensions(U, p)
        if xs:
            new_paths.update(xs)
        paths.add(p)  # add path to paths even if it has unreceived messages
        if verbose:
            print("{} paths, longest path: {}, unprocessed: {}".format(
                len(paths), longest_path, len(new_paths)), end='\n')
            if len(paths) % 1000 == 0:
                print(p)
        total_paths = len(paths)
    if verbose:
        print()
    return paths


def refines(U, params, Q, P, verbose=False):
    """Check that Q refines P"""

    U_Q = U + UoD.from_protocol(Q)
    U_P = U + UoD.from_protocol(P)

    p_keys = set()
    q_keys = set()
    for m in U_P.messages:
        p_keys.update(m.keys)
    for m in U_Q.messages:
        q_keys.update(m.keys)
    if not p_keys >= q_keys:
        return {
            "ok": False,
            "p_keys": p_keys,
            "q_keys": q_keys,
            "diff": p_keys.symmetric_difference(q_keys),
            "reason": "{} uses keys that do not appear in {}".format(P.name, Q.name)
        }

    paths_Q = all_paths(U_Q)
    paths_P = all_paths(U_P)

    longest_Q = longest_P = []
    for q in paths_Q:
        if len(q) > len(longest_Q):
            longest_Q = q
    for p in paths_P:
        if len(p) > len(longest_P):
            longest_P = p

    if verbose:
        print("{}: {} paths, longest path: {}".format(
            P.name, len(paths_P), longest_P))
        # print(paths_P)
        print("{}: {} paths, longest path: {}".format(
            Q.name, len(paths_Q), longest_Q))
        # print(paths_Q)

    checked = 0
    for q in paths_Q:
        # print("q: ", q)
        match = None
        for p in paths_P:
            # print("p: ", p)
            if subsumes(U_P, params, q, p, False):
                match = p
                # print("p branches: ", branches(U_P, p))
                # print("q branches: ", branches(U_Q, q))
                if not extensions(U_P, p) or extensions(U_Q, q):
                    break  # only try again if p has branches but q doesn't
        if match == None:
            return {
                "ok": False,
                "path": q,
                "reason": "{} has path that does not subsume any path in {}".format(Q.name, P.name)
            }
        if extensions(U_P, match) and not extensions(U_Q, q):
            #subsumes(U_P, params, q, match, True)
            return {
                "ok": False,
                "path": q,
                "match": match,
                "reason": "path in {} has branches, but path in {} does not".format(P.name, Q.name)
            }
        checked += 1
        if verbose:
            print("\r checked: {} of {} paths ({:.1f}%)".format(
                checked, len(paths_Q), checked / len(paths_Q) * 100), end='')
    if verbose:
        print()
    return {"ok": True}
