import logging
from .manticore import Manticore
from ..core.plugin import InstructionCounter, Visited, Tracer, RecordSymbolicBranches

logger = logging.getLogger("manticoreNative.main")


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


def native_main():
    args = parse_arguments()
    env = {key: val for key, val in [env[0].split("=") for env in args.env]}

    m = Manticore(
        args.argv[0],
        argv=args.argv[1:],
        env=env,
        entry_symbol=args.entrysymbol,
        workspace_url=args.workspace,
        policy=args.policy,
        concrete_start=args.data,
        pure_symbolic=args.pure_symbolic,
    )

    # Default plugins for now.. FIXME REMOVE!
    m.register_plugin(InstructionCounter())
    m.register_plugin(Visited(args.coverage))
    m.register_plugin(Tracer())
    m.register_plugin(RecordSymbolicBranches())

    if args.names is not None:
        m.apply_model_hooks(args.names)

    if args.assertions:
        m.load_assertions(args.assertions)

    @m.init
    def init(state):
        for file in args.files:
            state.platform.add_symbolic_file(file)

    with m.kill_timeout():
        m.run()

    m.finalize()
