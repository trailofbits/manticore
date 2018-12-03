from .manticore import Manticore
from ..core.plugin import InstructionCounter, Visited, Tracer, RecordSymbolicBranches


def native_main(args, logger_):
    env = {key: val for key, val in [env[0].split('=') for env in args.env]}

    m = Manticore(args.argv[0], argv=args.argv[1:], env=env, entry_symbol=args.entrysymbol,
                  workspace_url=args.workspace, policy=args.policy,
                  concrete_start=args.data, pure_symbolic=args.pure_symbolic, stdin_size=args.stdin_size)

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
