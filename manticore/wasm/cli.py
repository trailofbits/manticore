from .manticore import ManticoreWASM

from ..core.plugin import Profiler
from ..utils import config

consts = config.get_group("cli")
consts.add("target_func", default="main", description="WASM Function to execute")


def wasm_main(args, _logger):

    m = ManticoreWASM(
        args.argv[0],
        argv=args.argv[1:],
        env={},
        exec_start=True,
        workspace_url=args.workspace,
        policy=args.policy,
    )

    if consts.profile:
        profiler = Profiler()
        m.register_plugin(profiler)

    m.default_invoke(func_name=consts.target_func)

    with m.kill_timeout():
        m.run()

    m.finalize()

    return m
