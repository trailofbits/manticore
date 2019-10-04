from .manticore import ManticoreWASM


def wasm_main(args, _logger):

    m = ManticoreWASM(
        args.argv[0],
        argv=args.argv[1:],
        env={},
        entry_symbol=args.entrysymbol,  # TODO - this isn't supported yet
        workspace_url=args.workspace,
        policy=args.policy,
    )

    with m.kill_timeout():
        m.run()

    m.finalize()
