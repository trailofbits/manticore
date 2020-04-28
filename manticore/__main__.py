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
from .utils import config, log, install_helper, resources

consts = config.get_group("cli")
consts.add("recursionlimit", default=10000, description="Value to set for Python recursion limit")
consts.add("no-colors", default=True, description="Disable ANSI color escape sequences in output")
consts.add("verbosity", default=1, description="Specify verbosity level [1-4]")


if install_helper.has_native:
    from manticore.native.cli import native_main


def parse_arguments():
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

    parser = config.prepare_argument_parser(parser)

    parser.add_argument("--context", type=str, default=None, help=argparse.SUPPRESS)
    parser.add_argument(
        "--coverage", type=str, default="visited.txt", help="Where to write the coverage data"
    )
    parser.add_argument("--names", type=str, default=None, help=argparse.SUPPRESS)
    parser.add_argument("--offset", type=int, default=16, help=argparse.SUPPRESS)

    parser.add_argument(
        "argv",
        type=str,
        nargs="*",
        default=[],
        help="Path to program, and arguments ('+' in arguments indicates symbolic byte).",
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

    return config


def is_eth():
    for arg in sys.argv[1:]:
        if not arg.startswith("-") and (arg.endswith(".sol") or is_supported(arg)):
            return True
    return False


def is_wasm():
    for arg in sys.argv[1:]:
        if not arg.startswith("-") and (arg.endswith(".wasm") or arg.endswith(".wat")):
            return True
    return False


if __name__ == "__main__":
    """
    Dispatches execution into one of Manticore's engines: evm or native or wasm.
    """

    if is_eth():
        ethereum_main()
    elif is_wasm():
        wasm_main(args, logging.getLogger("manticore.main"))
    else:
        install_helper.ensure_native_deps()
        native_main(args, logging.getLogger("manticore.main"))
