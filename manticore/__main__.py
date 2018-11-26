"""
This is the Manticore's CLI `manticore` script.
"""
import argparse
import sys

import logging

from manticore.core.manticore import STDIN_INPUT_DEFAULT_SIZE
from .utils import config, log

consts = config.get_group('main')
consts.add('recursionlimit', default=10000,
           description="Value to set for Python recursion limit")
consts.add('timeout', default=0,
           description='Timeout, in seconds, for Manticore invocation')

# XXX(yan): This would normally be __name__, but then logger output will be pre-
# pended by 'm.__main__: ', which is not very pleasing. hard-coding to 'main'
logger = logging.getLogger('manticore.main')


def main():
    """
    Dispatches execution into one of Manticore's engines: evm or native.
    """
    log.init_logging()

    args = parse_arguments()

    if args.no_colors:
        log.disable_colors()

    sys.setrecursionlimit(consts.recursionlimit)

    log.set_verbosity(args.v)

    if args.argv[0].endswith('.sol'):
        from manticore.ethereum.cli import main as evm_main
        evm_main(args, logger)
    else:
        from manticore.native.cli import main as native_main
        native_main(args, logger)


def parse_arguments():
    def positive(value):
        ivalue = int(value)
        if ivalue <= 0:
            raise argparse.ArgumentTypeError("Argument must be positive")
        return ivalue

    parser = argparse.ArgumentParser(description='Symbolic execution tool', prog='manticore',
                                     formatter_class=argparse.ArgumentDefaultsHelpFormatter)
    parser.add_argument('--context', type=str, default=None,
                        help=argparse.SUPPRESS)
    parser.add_argument('--coverage', type=str, default=None,
                        help='Where to write the coverage data')
    parser.add_argument('--names', type=str, default=None,
                        help=argparse.SUPPRESS)
    parser.add_argument('--no-colors', action='store_true',
                        help='Disable ANSI color escape sequences in output')
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
    parser.add_argument('argv', type=str, nargs='*', default=[],
                        help="Path to program, and arguments ('+' in arguments indicates symbolic byte).")
    parser.add_argument('--timeout', type=int, default=consts.timeout,
                        help='Timeout. Abort exploration after TIMEOUT seconds')
    parser.add_argument('-v', action='count', default=1,
                        help='Specify verbosity level from -v to -vvvv')
    parser.add_argument('--workspace', type=str, default=None,
                        help=("A folder name for temporaries and results."
                              "(default mcore_?????)"))
    parser.add_argument('--version', action='version', version='Manticore 0.2.2',
                        help='Show program version information')
    parser.add_argument('--config', type=str,
                        help='Manticore config file (.yml) to use. (default config file pattern is: ./[.]m[anti]core.yml)')
    parser.add_argument('--stdin_size', type=int, default=STDIN_INPUT_DEFAULT_SIZE,
                        help='Control the maximum symbolic stdin size')

    bin_flags = parser.add_argument_group('Binary flags')
    bin_flags.add_argument('--entrysymbol', type=str, default=None,
                           help='Symbol as entry point')
    bin_flags.add_argument('--assertions', type=str, default=None,
                           help=argparse.SUPPRESS)
    bin_flags.add_argument('--buffer', type=str,
                           help=argparse.SUPPRESS)
    bin_flags.add_argument('--data', type=str, default='',
                           help='Initial concrete concrete_data for the input symbolic buffer')
    bin_flags.add_argument('--file', type=str, default=[], action='append', dest='files',
                           help='Specify symbolic input file, \'+\' marks symbolic bytes')
    bin_flags.add_argument('--env', type=str, nargs=1, default=[], action='append',
                           help='Add an environment variable. Use "+" for symbolic bytes. (VARNAME=++++)')

    eth_flags = parser.add_argument_group('Ethereum flags')
    eth_flags.add_argument('--verbose-trace', action='store_true',
                           help='Dump an extra verbose trace for each state')
    eth_flags.add_argument('--txlimit', type=positive,
                           help='Maximum number of symbolic transactions to run (positive integer)')

    eth_flags.add_argument('--txnocoverage', action='store_true',
                           help='Do not use coverage as stopping criteria')

    eth_flags.add_argument('--txnoether', action='store_true',
                           help='Do not attempt to send ether to contract')

    eth_flags.add_argument('--txaccount', type=str, default="attacker",
                           help='Account used as caller in the symbolic transactions, either "attacker" or "owner"')

    eth_flags.add_argument('--contract', type=str,
                           help='Contract name to analyze in case of multiple contracts')

    eth_flags.add_argument('--detect-overflow', action='store_true',
                           help='Enable integer overflow detection')

    eth_flags.add_argument('--detect-invalid', action='store_true',
                           help='Enable INVALID instruction detection')

    eth_flags.add_argument('--detect-uninitialized-memory', action='store_true',
                           help='Enable detection of uninitialized memory usage')

    eth_flags.add_argument('--detect-uninitialized-storage', action='store_true',
                           help='Enable detection of uninitialized storage usage')

    eth_flags.add_argument('--detect-reentrancy', action='store_true',
                           help='Enable detection of reentrancy bug')

    eth_flags.add_argument('--detect-reentrancy-advanced', action='store_true',
                           help='Enable detection of reentrancy bug -- this detector is better used via API')

    eth_flags.add_argument('--detect-unused-retval', action='store_true',
                           help='Enable detection of unused internal transaction return value')

    eth_flags.add_argument('--detect-delegatecall', action='store_true',
                           help='Enable detection of problematic uses of DELEGATECALL instruction')

    eth_flags.add_argument('--detect-selfdestruct', action='store_true',
                           help='Enable detection of reachable selfdestruct instructions')

    eth_flags.add_argument('--detect-externalcall', action='store_true',
                           help='Enable detection of reachable external call or ether leak to sender or arbitrary address')

    eth_flags.add_argument('--detect-env-instr', action='store_true',
                           help='Enable detection of use of potentially unsafe/manipulable instructions')

    eth_flags.add_argument('--detect-all', action='store_true',
                           help='Enable all detector heuristics')

    eth_flags.add_argument('--avoid-constant', action='store_true',
                           help='Avoid exploring constant functions for human transactions')

    eth_flags.add_argument('--detect-race-condition', action='store_true',
                           help='Enable detection of possible transaction race conditions'
                                ' (transaction order dependencies) (Ethereum only)')

    eth_flags.add_argument('--limit-loops', action='store_true',
                           help='Avoid exploring constant functions for human transactions')

    eth_flags.add_argument('--no-testcases', action='store_true',
                           help='Do not generate testcases for discovered states when analysis finishes')

    config_flags = parser.add_argument_group('Constants')
    config.add_config_vars_to_argparse(config_flags)

    parsed = parser.parse_args(sys.argv[1:])
    if parsed.procs <= 0:
        parsed.procs = 1

    config.process_config_values(parser, parsed)

    if not parsed.argv:
        print(parser.format_usage() + "error: the following arguments are required: argv")
        sys.exit(1)

    if parsed.policy.startswith('min'):
        parsed.policy = '-' + parsed.policy[3:]
    elif parsed.policy.startswith('max'):
        parsed.policy = '+' + parsed.policy[3:]

    return parsed


if __name__ == '__main__':
    main()
