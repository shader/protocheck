from protocheck.bspl import handle_enactability, handle_liveness, handle_safety, handle_atomicity, load_file, handle_projection
from protocheck.refinement import handle_refinement
from protocheck.node_red import handle_node_flow
import configargparse
import sys
import re


def handle_all(protocol, args, **kwargs):
    enactable = handle_enactability(protocol, args, **kwargs)
    if enactable:
        handle_liveness(protocol, args, **kwargs)
        handle_safety(protocol, args, **kwargs)
        handle_atomicity(protocol, args, **kwargs)


def check_syntax(*args):
    print("Syntax: correct")

# Actions that only take one argument, and therefore can be repeated for each input file
unary_actions = {
    'enactability': handle_enactability,
    'liveness': handle_liveness,
    'safety': handle_safety,
    'atomicity': handle_atomicity,
    'syntax': check_syntax,
    'flow': handle_node_flow,
    'all': handle_all
}

# Actions with more complex argument schemes
actions = {
    'refinement': handle_refinement,
    'projection': handle_projection
}


def main():

    parser = configargparse.get_argument_parser()
    parser.description = 'BSPL Protocol property checker'
    parser.add('-s', '--stats', action="store_true",
               help='Print statistics')
    parser.add('-v', '--verbose', action="store_true",
               help='Print additional details: spec, formulas, stats, etc.')
    parser.add('-q', '--quiet', action="store_true",
               help='Prevent printing of violation and formula output')
    parser.add('-f', '--filter', default='.*',
               help='Only process protocols matching regexp')
    parser.add('--version', action="store_true", help='Print version number')
    parser.add('--debug', action="store_true", help='Debug mode')
    parser.add('action', help='Primary action to perform',
               choices=set(actions.keys()).union(unary_actions.keys()))
    parser.add('input', nargs='+',
               help='additional parameters or protocol description file(s)')

    if '--version' in sys.argv:
        print(__version__)
        sys.exit(0)
    else:
        args = parser.parse()
        global debug
        debug = args.debug

    if args.action in unary_actions:
        # unary actions only take one argument, and are therefore repeated for each argument
        for path in args.input:
            spec = load_file(path)
            for protocol in spec.protocols.values():
                if re.match(args.filter, protocol.name):
                    print("%s (%s): " % (protocol.name, path))
                    unary_actions[args.action](protocol, args)
                    print()

            if not spec.protocols:
                print("No protocols parsed from file: ", args.input)
    else:
        actions[args.action](args)


if __name__ == "__main__":
    main()
