from protocheck.bspl import load_file


def handle_refinement(args):
    path = args.input[0]
    spec = load_file(path)
    Q = P = None
    for protocol in spec.protocols.values():
        if protocol.name == args.input[1]:
            Q = protocol
        elif protocol.name == args.input[2]:
            P = protocol

    return check_refinement(Q, P)


def check_refinement(Q, P):
    """Check that protocol Q refines protocol P"""

    return refines(UoD(), P.params, Q, P).result == True


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


def known(path, R):
    """Compute the set of parameters observed by role R after enacting path"""
    time = 0
    k = set()
    for instance in path:
        if (instance.msg.sender == R
                or instance.msg.recipient == R and instance.delay + time <= len(path)):
            k.update(set(instance.msg.ins))
            k.update(set(instance.msg.outs))
        time += 1
    return k


def viable(path, msg):
    k = known(path, msg.sender)
    return k == msg.ins and k.intersection(msg.outs) == set()


class UoD():
    def __init__(self, messages={}, roles={}):
        self.messages = set(messages)
        self.roles = set(roles)

    @staticmethod
    def from_protocol(protocol):
        return UoD(protocol.messages.values(), protocol.roles.values())

    def __add__(self, other):
        return UoD(self.messages.union(other.messages), self.roles.union(other.roles))


def branches(U, path):
    b = set()
    for msg in U.messages:
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
    return set(i.msg.sender for i in path if p in i.msg.outs)


def subsumes(U, params, a, b):
    """Path a subsumes path b"""
    for p in params:
        if sources(a, p) != sources(b, p):
            return False
    for r in U.roles:
        if known(a, r).intersection(params) != known(b, r).intersection(params):
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


def refines(U, params, Q, P):
    U_Q = U + UoD.from_protocol(Q)
    U_P = U + UoD.from_protocol(P)

    paths_Q = all_paths(U_Q)
    paths_P = all_paths(U_P)

    for q in paths_Q:
        match = None
        for p in paths_P:
            if subsumes(U_Q, params, q, p):
                match = p
        if not match:
            return {
                "result": False,
                "path": q,
                "reason": "Q has path that does subsume anything in P"
            }
        elif branches(U_P, match) and not branches(U_Q, q):
            return {
                result: False,
                path: q,
                match: match,
                reason: "P has branches but Q does not"
            }
    return {"result": True}
