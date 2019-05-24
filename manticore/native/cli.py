from .manticore import Manticore
from ..core.plugin import InstructionCounter, Visited, Tracer, RecordSymbolicBranches


def native_main(args, _logger):
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
