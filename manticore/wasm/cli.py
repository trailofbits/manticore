from .manticore import ManticoreWASM


def wasm_main(args, _logger):
    env = {key: val for key, val in [env[0].split("=") for env in args.env]}

    m = ManticoreWASM(
        args.argv[0],
        argv=args.argv[1:],
        env=env,
        entry_symbol=args.entrysymbol,
        workspace_url=args.workspace,
        policy=args.policy,
    )

    with m.kill_timeout():
        m.run()

    m.finalize()
