import sys
import logging
import argparse

from . import Manticore
from .utils import log

# XXX(yan): This would normally be __name__, but then logger output will be pre-
# pended by 'm.__main__: ', which is not very pleasing. hard-coding to 'main'
logger = logging.getLogger('manticore.main')

sys.setrecursionlimit(10000)


def parse_arguments():
    def positive(value):
        ivalue = int(value)
        if ivalue <= 0:
            raise argparse.ArgumentTypeError("Argument must be positive")
        return ivalue

    parser = argparse.ArgumentParser(description='Symbolic execution tool')
    parser.add_argument('--assertions', type=str, default=None,
                        help=argparse.SUPPRESS)
    parser.add_argument('--buffer', type=str,
                        help=argparse.SUPPRESS)
    parser.add_argument('--context', type=str, default=None,
                        help=argparse.SUPPRESS)
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
                        help=argparse.SUPPRESS)
    parser.add_argument('--offset', type=int, default=16,
                        help=argparse.SUPPRESS)
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
    parser.add_argument('--timeout', type=int, default=0,
                        help='Timeout. Abort exploration aftr TIMEOUT seconds')
    parser.add_argument('-v', action='count', default=1,
                        help='Specify verbosity level from -v to -vvvv')
    parser.add_argument('--workspace', type=str, default=None,
                        help=("A folder name for temporaries and results."
                              "(default mcore_?????)"))
    parser.add_argument('--version', action='version', version='Manticore 0.1.7',
                         help='Show program version information')
    parser.add_argument('--txlimit', type=positive,
                        help='Maximum number of symbolic transactions to run (positive integer) (Ethereum only)')
    parser.add_argument('--contract', type=str,
                        help='Contract name to analyze in case of multiple ones (Ethereum only)')

    parsed = parser.parse_args(sys.argv[1:])
    if parsed.procs <= 0:
        parsed.procs = 1

    if parsed.policy.startswith('min'):
        parsed.policy = '-' + parsed.policy[3:]
    elif parsed.policy.startswith('max'):
        parsed.policy = '+' + parsed.policy[3:]

    return parsed


def ethereum_cli(args):
    from ethereum import ManticoreEVM, IntegerOverflow, UninitializedStorage, UninitializedMemory
    log.init_logging()

    m = ManticoreEVM(procs=args.procs)

    ################ Default? Detectors #######################
    m.register_detector(IntegerOverflow())
    m.register_detector(UninitializedStorage())
    m.register_detector(UninitializedMemory())

    logger.info("Beginning analysis")

    m.multi_tx_analysis(args.argv[0], args.contract, args.txlimit)

def main():
    log.init_logging()
    args = parse_arguments()

    Manticore.verbosity(args.v)

    # TODO(mark): Temporarily hack ethereum support into manticore cli
    if args.argv[0].endswith('.sol'):
        ethereum_cli(args)
        return

    env = {key:val for key, val in map(lambda env: env[0].split('='), args.env)}

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
