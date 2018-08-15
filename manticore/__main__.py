import copy
import os

import sys
import logging
import argparse
from configparser import ConfigParser, NoSectionError
from manticore import config
import manticore.config

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

    conf_parser = argparse.ArgumentParser(
        description=__doc__,
        formatter_class=argparse.RawDescriptionHelpFormatter,
        add_help=False
    )
    conf_parser.add_argument("--config",
                             help="Specify config file", metavar="FILE")
    args, remaining_argv = conf_parser.parse_known_args()
    defaults = copy.deepcopy(config.defaults)
    defaults.update(dict(config._config(path=args.config).items('settings')))

    parser = argparse.ArgumentParser(parents=[conf_parser], description='Symbolic execution tool')
    parser.set_defaults(**defaults)

    parser.add_argument('--cache-dict-max-size', type=int, help=argparse.SUPPRESS)
    parser.add_argument('--cache-dict-flush-perc', type=int, help=argparse.SUPPRESS)
    parser.add_argument('--assertions', type=str, help=argparse.SUPPRESS)
    parser.add_argument('--buffer', type=str, help=argparse.SUPPRESS)
    parser.add_argument('--context', type=str, help=argparse.SUPPRESS)
    parser.add_argument('--coverage', type=str, help='where to write the coverage data')
    parser.add_argument('--data', type=str, default='',
                        help='Initial concrete concrete_data for the input symbolic buffer')
    parser.add_argument('--env', type=str, nargs=1, action='append',
                        help='Add an environment variable. Use "+" for symbolic bytes. (VARNAME=++++)')
    #TODO allow entry as an address
    #parser.add_argument('--entry', type=str, default=None,
    #                    help='address as entry point')
    parser.add_argument('--entrysymbol', type=str, help='symbol as entry point')
    parser.add_argument('--file', type=str, action='append', dest='files',
                        help='Specify symbolic input file, \'+\' marks symbolic bytes')
    parser.add_argument('--names', type=str, help=argparse.SUPPRESS)
    parser.add_argument('--offset', type=int, help=argparse.SUPPRESS)
    # FIXME (theo) Add some documentation on the different search policy options
    parser.add_argument('--policy', type=str,
                        help=("Search policy. random|adhoc|uncovered|dicount"
                              "|icount|syscount|depth. (use + (max) or - (min)"
                              " to specify order. e.g. +random)"))
    parser.add_argument('--profile', action='store_true',
                        help='Enable profiling mode.')
    parser.add_argument('--procs', type=int, help='Number of parallel processes to spawn')
    parser.add_argument('--solver-timeout', type=int, help='timeout for solver in milliseconds')
    parser.add_argument('argv', type=str, nargs='+',
                        help="Path to program, and arguments ('+' in arguments indicates symbolic byte).")
    parser.add_argument('--timeout', type=int,
                        help='Timeout. Abort exploration aftr TIMEOUT seconds')
    parser.add_argument('-v', action='count',
                        help='Specify verbosity level from -v to -vvvv')
    parser.add_argument('--workspace', type=str,
                        help=("A folder name for temporaries and results."
                              "(default mcore_?????)"))
    parser.add_argument('--version', action='version', version='Manticore 0.2.0',
                        help='Show program version information')
    parser.add_argument('--txlimit', type=positive,
                        help='Maximum number of symbolic transactions to run (positive integer) (Ethereum only)')

    parser.add_argument('--txnocoverage', action='store_true',
                        help='Do not use coverage as stopping criteria (Ethereum only)')

    parser.add_argument('--txaccount', type=str,
                        help='Account used as caller in the symbolic transactions, either "attacker" or "owner" (Ethereum only)')

    parser.add_argument('--contract', type=str,
                        help='Contract name to analyze in case of multiple ones (Ethereum only)')

    parser.add_argument('--detect-overflow', action='store_true',
                        help='Enable integer overflow detection (Ethereum only)')

    parser.add_argument('--detect-invalid', action='store_true',
                        help='Enable INVALID instruction detection (Ethereum only)')

    parser.add_argument('--detect-uninitialized-memory', action='store_true',
                        help='Enable detection of uninitialized memory usage (Ethereum only)')

    parser.add_argument('--detect-uninitialized-storage', action='store_true',
                        help='Enable detection of uninitialized storage usage (Ethereum only)')

    parser.add_argument('--detect-reentrancy', action='store_true',
                        help='Enable detection of reentrancy bug (Ethereum only)')

    parser.add_argument('--detect-unused-retval', action='store_true',
                        help='Enable detection of not used internal transaction return value')

    parser.add_argument('--detect-all', action='store_true',
                        help='Enable all detector heuristics (Ethereum only)')

    parser.add_argument('--avoid-constant', action='store_true',
                        help='Avoid exploring constant functions for human transactions (Ethereum only)')

    parsed = parser.parse_args(remaining_argv)
    defaults.update(parsed.__dict__)
    config.settings.update(defaults)
    parsed = argparse.Namespace(**defaults)
    if parsed.procs <= 0:
        parsed.procs = 1

    if parsed.policy.startswith('min'):
        parsed.policy = '-' + parsed.policy[3:]
    elif parsed.policy.startswith('max'):
        parsed.policy = '+' + parsed.policy[3:]

    return parsed


def ethereum_cli(args):
    from .ethereum import ManticoreEVM, DetectInvalid, DetectIntegerOverflow, DetectUninitializedStorage, DetectUninitializedMemory, FilterFunctions, DetectReentrancy, DetectUnusedRetVal
    log.init_logging()

    m = ManticoreEVM(procs=args.procs)

    if args.detect_all or args.detect_invalid:
        m.register_detector(DetectInvalid())
    if args.detect_all or args.detect_overflow:
        m.register_detector(DetectIntegerOverflow())
    if args.detect_all or args.detect_uninitialized_storage:
        m.register_detector(DetectUninitializedStorage())
    if args.detect_all or args.detect_uninitialized_memory:
        m.register_detector(DetectUninitializedMemory())
    if args.detect_all or args.detect_reentrancy:
        m.register_detector(DetectReentrancy())
    if args.detect_all or args.detect_unused_retval:
        m.register_detector(DetectUnusedRetVal())

    if args.avoid_constant:
        # avoid all human level tx that has no effect on the storage
        filter_nohuman_constants = FilterFunctions(regexp=r".*", depth='human', mutability='constant', include=False)
        m.register_plugin(filter_nohuman_constants)

    logger.info("Beginning analysis")

    m.multi_tx_analysis(args.argv[0], contract_name=args.contract, tx_limit=args.txlimit, tx_use_coverage=not args.txnocoverage, tx_account=args.txaccount)

    #TODO unregister all plugins
    m.finalize()


def main():
    from .manticore import InstructionCounter, Visited, Tracer, RecordSymbolicBranches

    log.init_logging()
    args = parse_arguments()

    Manticore.verbosity(args.v)

    # TODO(mark): Temporarily hack ethereum support into manticore cli
    if args.argv[0].endswith('.sol'):
        ethereum_cli(args)
        return

    env = {key: val for key, val in [env[0].split('=') for env in args.env]}

    m = Manticore(args.argv[0], argv=args.argv[1:], env=env, entry_symbol=args.entrysymbol, workspace_url=args.workspace, policy=args.policy, concrete_start=args.data)

    # Default plugins for now.. FIXME REMOVE!
    m.register_plugin(InstructionCounter())
    m.register_plugin(Visited())
    m.register_plugin(Tracer())
    m.register_plugin(RecordSymbolicBranches())

    # Fixme(felipe) remove this, move to plugin
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
