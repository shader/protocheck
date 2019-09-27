from protocheck.bspl import handle_enactability, handle_liveness, handle_safety, handle_atomicity, load_file
from protocheck.refinement import handle_refinement
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


actions = {
    'enactability': handle_enactability,
    'liveness': handle_liveness,
    'safety': handle_safety,
    'atomicity': handle_atomicity,
    'syntax': check_syntax,
    'refinement': handle_refinement,
    'all': handle_all
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
               choices=actions.keys())
    parser.add('input', nargs='+', help='Protocol description file(s)')

    if '--version' in sys.argv:
        print(__version__)
        sys.exit(0)
    else:
        args = parser.parse()
        global debug
        debug = args.debug

    if args.action == "refinement":
        actions[args.action](args)
    else:
        for path in args.input:
            spec = load_file(path)
            for protocol in spec.protocols.values():
                if re.match(args.filter, protocol.name):
                    print("%s (%s): " % (protocol.name, path))
                    actions[args.action](protocol, args)
                    print()

            if not spec.protocols:
                print("No protocols parsed from file: ", args.input)


if __name__ == "__main__":
    main()
