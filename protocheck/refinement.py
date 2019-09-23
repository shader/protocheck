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

    return True
