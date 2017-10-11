import sys
import argparse
import logging
from manticore import Manticore, log, make_initial_state

sys.setrecursionlimit(10000)

def parse_arguments():
    ###########################################################################
    # parse arguments
    parser = argparse.ArgumentParser(description='Symbolically analyze a program')
    parser.add_argument('--assertions', type=str, default=None,
                        help='File with additional assertions')
    parser.add_argument('--buffer', type=str,
                        help='Specify buffer to make symbolic')
    parser.add_argument('--context', type=str, default=None,
                        help='path to file with additional context')
    parser.add_argument('--coverage', type=str, default=None,
                        help='where to write the coverage data')
    parser.add_argument('--data', type=str, default='',
                        help='Initial concrete concrete_data for the input symbolic buffer')
    # FIXME (theo) similarly to policy, add documentation here.
    disas = ['capstone', 'binja-il']
    parser.add_argument('--disasm', type=str, default='capstone', choices=disas,
                        help=argparse.SUPPRESS)
    parser.add_argument('--env', type=str, nargs=1, default=[], action='append',
                        help='Specify symbolic environment variable VARNAME=++++++')
    parser.add_argument('--file', type=str, default=[], action='append', dest='files',
                        help='Specify symbolic input file, \'+\' marks symbolic bytes')
    parser.add_argument('--names', type=str, default=None,
                        help=("File with function addresses to replace "
                              "with known models"))
    parser.add_argument('--offset', type=int, default=16,
                        help='Buffer header size to leave concrete')
    # FIXME (theo) Add some documentation on the different search policy options
    parser.add_argument('--policy', type=str, default='random',
                        help=("Search policy. random|adhoc|uncovered|dicount"
                              "|icount|syscount|depth. (use + (max) or - (min)"
                              " to specify order. e.g. +random)"))
    parser.add_argument('--profile', action='store_true',
                        help='Enable profiling mode.')
    parser.add_argument('--procs', type=int, default=1,
                        help='Number of parallel processes to spawn')
    parser.add_argument('argv', type=str, nargs='+',
                        help="Path to program, and arguments ('+' in arguments indicates symbolic byte).")
    parser.add_argument('--replay', type=str, default=None,
                        help='The trace filename to replay')
    parser.add_argument('--size', type=str, help='Specify buffer full size')
    parser.add_argument('--timeout', type=int, default=0,
                        help='Timeout. Abort exploration aftr TIMEOUT seconds')
    parser.add_argument('-v', action='count', default=1,
                        help='Specify verbosity level from -v to -vvvv')
    parser.add_argument('--workspace', type=str, default=None,
                        help=("A folder name for temporaries and results."
                              "(default mcore_?????)"))

    parsed = parser.parse_args(sys.argv[1:])
    if parsed.procs <= 0:
        parsed.procs = 1

    if parsed.policy.startswith('min'):
        parsed.policy = '-' + parsed.policy[3:]
    elif parsed.policy.startswith('max'):
        parsed.policy = '+' + parsed.policy[3:]

    return parsed

def main():
    args = parse_arguments()

    env = {key:val for key, val in map(lambda env: env[0].split('='), args.env)}

    Manticore.verbosity(args.v)

    m = Manticore(args.argv[0], argv=args.argv[1:], env=env, workspace_url=args.workspace,  policy=args.policy, disasm=args.disasm)

    #Fixme(felipe) remove this, move to plugin
    m.coverage_file = args.coverage

    if args.names is not None:
        m.apply_model_hooks(args.names)

    if args.assertions:
        m.load_assertions(args.assertions)

    @m.init
    def init(initial_state):
        for file in args.files:
            initial_state.platform.add_symbolic_file(file)

    m.run(procs=args.procs, timeout=args.timeout, should_profile=args.profile)

if __name__ == '__main__':
    main()
