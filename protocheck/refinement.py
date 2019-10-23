from protocheck.bspl import load_file, Message, Role


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
    return []


class Instance():
    def __init__(self, msg, delay=float('inf')):
        self.msg = msg
        self.delay = delay

    def __str__(self):
        return "({},{})".format(self.msg.name, self.delay)

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


def total_keys(path):
    keys = set()
    for i in path:
        keys.update(i.msg.keys)
    return keys


def known(path, keys, R):
    """Compute the set of parameters observed by role R after enacting path"""
    time = 0
    k = set()
    for instance in path:
        if (instance.msg.keys >= keys
            and (instance.msg.sender.name == R.name
                 or (instance.msg.recipient.name == R.name
                     and instance.delay + time <= len(path)))):
            k.update(set(instance.msg.ins))
            k.update(set(instance.msg.outs))
        time += 1
    return k


def viable(path, msg):
    k = known(path, msg.keys, msg.sender)
    return k.issuperset(msg.ins) and k.intersection(msg.outs) == set()


class UoD():
    def __init__(self, messages={}, roles={}):
        self.messages = set(messages)
        self.roles = set(roles)

    @staticmethod
    def from_protocol(protocol):
        external = Role({'name': '*External*'}, protocol.parent)
        protocol.roles[external.name] = external
        dependencies = {}
        for p in protocol.ins.union(protocol.nils):
            # generate messages that provide p to each sender
            for m in protocol.messages.values():
                if p in m.parameters and not p in dependencies:
                    schema = {
                        'name': p + '-source',
                        'sender': external.name,
                        'recipient': m.sender.name,
                        'parameters': [m.parameters[k].schema for k in protocol.keys if k is not p] + [{'adornment': 'out', 'name': p, 'key': m.parameters[p].key}]
                    }
                    dependencies[p] = Message(schema, protocol)
        uod = UoD(list(protocol.messages.values()) + list(dependencies.values()),
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
            b.add(Instance(msg, float("inf")))
    return b


def unreceived(path):
    return set(i for i in path if i.delay == float("inf"))


def extensions(U, path):
    extended = [path + [b] for b in branches(U, path)]
    for u in unreceived(path):
        p = path.copy()
        i = p.index(u)
        p[i] = Instance(u.msg, len(p) - i - 1)
        extended.append(p)
    return extended


def sources(path, p):
    """The set of all roles that produce p as an out parameter in path"""
    return set(i.msg.sender.name for i in path if p in i.msg.outs)


def subsumes(U, params, a, b):
    """Path a subsumes path b"""
    for p in params:
        sources_a = sources(a, p)
        sources_b = sources(b, p)
        if sources_a != sources_b:
            # print("sources don't match: {} != {}".format(sources_a, sources_b))
            return False
    for r in U.roles:
        known_a = known(a, total_keys(a), r).intersection(params)
        known_b = known(b, total_keys(a), r).intersection(params)
        if known_a != known_b:
            print("{}'s knowledge doesn't match: {} != {}".format(
                r.name, known_a, known_b))
            return False
    if len(b) > 1:
        b2 = b[:-1]
        return any(subsumes(U, params, a[:end], b2) for end in range(len(a)))
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


def all_paths(U):
    paths = []
    new_paths = [empty_path()]
    while len(new_paths):
        p = new_paths.pop()
        xs = extensions(U, p)
        if xs:
            new_paths.extend(xs)
        if not unreceived(p):
            paths.insert(len(paths), p)
    return paths


def refines(U, params, Q, P, verbose=False):
    """Check that Q refines P"""
    U_Q = U + UoD.from_protocol(Q)
    U_P = U + UoD.from_protocol(P)

    paths_Q = all_paths(U_Q)
    paths_P = all_paths(U_P)

    if verbose:
        print("{} paths: ".format(Q.name), paths_Q)
        print("{} paths: ".format(P.name), paths_P)

    for q in paths_Q:
        # print("q: ", q)
        match = None
        for p in paths_P:
            # print("p: ", p)
            if subsumes(U_Q, params, q, p):
                # print("q subsumes p")
                match = p
                break
        if match == None:
            return {
                "ok": False,
                "path": q,
                "reason": "{} has path that does not subsume any path in {}".format(Q.name, P.name)
            }
        elif branches(U_P, match) and not branches(U_Q, q):
            return {
                "ok": False,
                "path": q,
                "match": match,
                "reason": "path in {} has branches, but path in {} does not".format(P.name, Q.name)
            }
    return {"ok": True}
