"""
This is the Manticore's CLI `manticore` script.
"""
import argparse
import logging
import sys

import pkg_resources

from crytic_compile import is_supported, cryticparser
from .core.manticore import ManticoreBase, set_verbosity
from .ethereum.cli import ethereum_main
from .wasm.cli import wasm_main
from .utils import config, log, install_helper

consts = config.get_group("main")
consts.add("recursionlimit", default=10000, description="Value to set for Python recursion limit")


# XXX(yan): This would normally be __name__, but then logger output will be pre-
# pended by 'm.__main__: ', which is not very pleasing. hard-coding to 'main'
logger = logging.getLogger("manticore.main")

if install_helper.has_native:
    from manticore.native.cli import native_main


def main() -> None:
    """
    Dispatches execution into one of Manticore's engines: evm or native.
    """
    log.init_logging()
    args = parse_arguments()

    if args.no_colors:
        log.disable_colors()

    sys.setrecursionlimit(consts.recursionlimit)

    set_verbosity(args.v)

    if args.argv[0].endswith(".sol") or is_supported(args.argv[0]):
        ethereum_main(args, logger)
    elif args.argv[0].endswith(".wasm") or args.argv[0].endswith(".wat"):
        wasm_main(args, logger)
    else:
        install_helper.ensure_native_deps()
        native_main(args, logger)


def parse_arguments() -> argparse.Namespace:
    def positive(value):
        ivalue = int(value)
        if ivalue <= 0:
            raise argparse.ArgumentTypeError("Argument must be positive")
        return ivalue

    parser = argparse.ArgumentParser(
        description="Symbolic execution tool",
        prog="manticore",
        formatter_class=argparse.ArgumentDefaultsHelpFormatter,
    )

    # Add crytic compile arguments
    # See https://github.com/crytic/crytic-compile/wiki/Configuration
    cryticparser.init(parser)

    parser.add_argument("--context", type=str, default=None, help=argparse.SUPPRESS)
    parser.add_argument(
        "--coverage", type=str, default="visited.txt", help="Where to write the coverage data"
    )
    parser.add_argument("--names", type=str, default=None, help=argparse.SUPPRESS)
    parser.add_argument(
        "--no-colors", action="store_true", help="Disable ANSI color escape sequences in output"
    )
    parser.add_argument("--offset", type=int, default=16, help=argparse.SUPPRESS)
    # FIXME (theo) Add some documentation on the different search policy options
    parser.add_argument(
        "--policy",
        type=str,
        default="random",
        help=(
            "Search policy. random|adhoc|uncovered|dicount"
            "|icount|syscount|depth. (use + (max) or - (min)"
            " to specify order. e.g. +random)"
        ),
    )
    parser.add_argument(
        "argv",
        type=str,
        nargs="*",
        default=[],
        help="Path to program, and arguments ('+' in arguments indicates symbolic byte).",
    )
    parser.add_argument(
        "-v", action="count", default=1, help="Specify verbosity level from -v to -vvvv"
    )
    parser.add_argument(
        "--workspace",
        type=str,
        default=None,
        help=("A folder name for temporaries and results." "(default mcore_?????)"),
    )

    current_version = pkg_resources.get_distribution("manticore").version
    parser.add_argument(
        "--version",
        action="version",
        version=f"Manticore {current_version}",
        help="Show program version information",
    )
    parser.add_argument(
        "--config",
        type=str,
        help="Manticore config file (.yml) to use. (default config file pattern is: ./[.]m[anti]core.yml)",
    )

    bin_flags = parser.add_argument_group("Binary flags")
    bin_flags.add_argument("--entrysymbol", type=str, default=None, help="Symbol as entry point")
    bin_flags.add_argument("--assertions", type=str, default=None, help=argparse.SUPPRESS)
    bin_flags.add_argument("--buffer", type=str, help=argparse.SUPPRESS)
    bin_flags.add_argument(
        "--data",
        type=str,
        default="",
        help="Initial concrete concrete_data for the input symbolic buffer",
    )
    bin_flags.add_argument(
        "--file",
        type=str,
        default=[],
        action="append",
        dest="files",
        help="Specify symbolic input file, '+' marks symbolic bytes",
    )
    bin_flags.add_argument(
        "--env",
        type=str,
        nargs=1,
        default=[],
        action="append",
        help='Add an environment variable. Use "+" for symbolic bytes. (VARNAME=++++)',
    )
    bin_flags.add_argument(
        "--pure-symbolic", action="store_true", help="Treat all writable memory as symbolic"
    )

    eth_flags = parser.add_argument_group("Ethereum flags")
    eth_flags.add_argument(
        "--verbose-trace", action="store_true", help="Dump an extra verbose trace for each state"
    )
    eth_flags.add_argument(
        "--txlimit",
        type=positive,
        help="Maximum number of symbolic transactions to run (positive integer)",
    )

    eth_flags.add_argument(
        "--txnocoverage", action="store_true", help="Do not use coverage as stopping criteria"
    )

    eth_flags.add_argument(
        "--txnoether", action="store_true", help="Do not attempt to send ether to contract"
    )

    eth_flags.add_argument(
        "--txaccount",
        type=str,
        default="attacker",
        help='Account used as caller in the symbolic transactions, either "attacker" or '
        '"owner" or "combo1" (uses both)',
    )

    eth_flags.add_argument(
        "--txpreconstrain",
        action="store_true",
        help="Constrain human transactions to avoid exceptions in the contract function dispatcher",
    )

    eth_flags.add_argument(
        "--contract", type=str, help="Contract name to analyze in case of multiple contracts"
    )

    eth_detectors = parser.add_argument_group("Ethereum detectors")

    eth_detectors.add_argument(
        "--list-detectors",
        help="List available detectors",
        action=ListEthereumDetectors,
        nargs=0,
        default=False,
    )

    eth_detectors.add_argument(
        "--exclude",
        help="Comma-separated list of detectors that should be excluded",
        action="store",
        dest="detectors_to_exclude",
        default="",
    )

    eth_detectors.add_argument(
        "--exclude-all", help="Excludes all detectors", action="store_true", default=False
    )

    eth_flags.add_argument(
        "--avoid-constant",
        action="store_true",
        help="Avoid exploring constant functions for human transactions",
    )

    eth_flags.add_argument(
        "--limit-loops",
        action="store_true",
        help="Limit loops depth",
    )

    eth_flags.add_argument(
        "--no-testcases",
        action="store_true",
        help="Do not generate testcases for discovered states when analysis finishes",
    )

    eth_flags.add_argument(
        "--only-alive-testcases",
        action="store_true",
        help="Do not generate testcases for invalid/throwing states when analysis finishes",
    )

    eth_flags.add_argument(
        "--thorough-mode",
        action="store_true",
        help="Configure Manticore for more exhaustive exploration. Evaluate gas, generate testcases for dead states, "
        "explore constant functions, and run a small suite of detectors.",
    )

    config_flags = parser.add_argument_group("Constants")
    config.add_config_vars_to_argparse(config_flags)

    parsed = parser.parse_args(sys.argv[1:])
    config.process_config_values(parser, parsed)

    if not parsed.argv:
        print(parser.format_usage() + "error: the following arguments are required: argv")
        sys.exit(1)

    if parsed.policy.startswith("min"):
        parsed.policy = "-" + parsed.policy[3:]
    elif parsed.policy.startswith("max"):
        parsed.policy = "+" + parsed.policy[3:]

    return parsed


class ListEthereumDetectors(argparse.Action):
    def __call__(self, parser, *args, **kwargs):
        from .ethereum.cli import get_detectors_classes
        from .utils.command_line import output_detectors

        output_detectors(get_detectors_classes())
        parser.exit()


if __name__ == "__main__":
    # Only print with Manticore's logger
    logging.getLogger().handlers = []
    main()
