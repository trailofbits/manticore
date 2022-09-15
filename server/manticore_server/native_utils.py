import argparse
import shlex

import pkg_resources
from manticore.utils import config
from manticore.utils.log import set_verbosity


def parse_native_arguments(additional_args: str) -> argparse.Namespace:
    """parse additional arguments for manticore native execution, CLI-style"""

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

    parser.add_argument("--context", type=str, default=None, help=argparse.SUPPRESS)
    parser.add_argument(
        "--coverage",
        type=str,
        default="visited.txt",
        help="Where to write the coverage data",
    )
    parser.add_argument("--names", type=str, default=None, help=argparse.SUPPRESS)
    parser.add_argument(
        "--no-colors",
        action="store_true",
        help="Disable ANSI color escape sequences in output",
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
    bin_flags.add_argument(
        "--entrysymbol", type=str, default=None, help="Symbol as entry point"
    )
    bin_flags.add_argument(
        "--assertions", type=str, default=None, help=argparse.SUPPRESS
    )
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
        "--pure-symbolic",
        action="store_true",
        help="Treat all writable memory as symbolic",
    )

    config_flags = parser.add_argument_group("Constants")
    config.add_config_vars_to_argparse(config_flags)

    parsed = parser.parse_args(shlex.split(additional_args))
    config.process_config_values(parser, parsed)

    if parsed.policy.startswith("min"):
        parsed.policy = "-" + parsed.policy[3:]
    elif parsed.policy.startswith("max"):
        parsed.policy = "+" + parsed.policy[3:]

    set_verbosity(parsed.v)

    return parsed
