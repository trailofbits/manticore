from manticore.ethereum.detectors import DetectInvalid, DetectIntegerOverflow, DetectUninitializedStorage, \
    DetectUninitializedMemory, DetectReentrancySimple, DetectReentrancyAdvanced, \
    DetectUnusedRetVal, DetectSelfdestruct, DetectDelegatecall, \
    DetectExternalCallAndLeak, DetectEnvInstruction, DetectRaceCondition
from manticore.ethereum.manticore import ManticoreEVM
from manticore.ethereum.plugins import FilterFunctions, LoopDepthLimiter, VerboseTrace


def evm_main(args, logger):
    m = ManticoreEVM(procs=args.procs, workspace_url=args.workspace)

    m.verbosity(args.v)

    if args.detect_all or args.detect_invalid:
        m.register_detector(DetectInvalid())
    if args.detect_all or args.detect_overflow:
        m.register_detector(DetectIntegerOverflow())
    if args.detect_all or args.detect_uninitialized_storage:
        m.register_detector(DetectUninitializedStorage())
    if args.detect_all or args.detect_uninitialized_memory:
        m.register_detector(DetectUninitializedMemory())
    if args.detect_all or args.detect_reentrancy:
        m.register_detector(DetectReentrancySimple())
    if args.detect_reentrancy_advanced:
        m.register_detector(DetectReentrancyAdvanced())
    if args.detect_all or args.detect_unused_retval:
        m.register_detector(DetectUnusedRetVal())
    if args.detect_all or args.detect_delegatecall:
        m.register_detector(DetectDelegatecall())
    if args.detect_all or args.detect_selfdestruct:
        m.register_detector(DetectSelfdestruct())
    if args.detect_all or args.detect_externalcall:
        m.register_detector(DetectExternalCallAndLeak())
    if args.detect_all or args.detect_env_instr:
        m.register_detector(DetectEnvInstruction())
    if args.detect_all or args.detect_race_condition:
        m.register_detector(DetectRaceCondition())

    if args.verbose_trace:
        m.register_plugin(VerboseTrace())

    if args.limit_loops:
        m.register_plugin(LoopDepthLimiter())

    if args.avoid_constant:
        # avoid all human level tx that has no effect on the storage
        filter_nohuman_constants = FilterFunctions(regexp=r".*", depth='human', mutability='constant', include=False)
        m.register_plugin(filter_nohuman_constants)

    logger.info("Beginning analysis")

    with m.shutdown_timeout(args.timeout):
        m.multi_tx_analysis(args.argv[0], contract_name=args.contract, tx_limit=args.txlimit, tx_use_coverage=not args.txnocoverage, tx_send_ether=not args.txnoether, tx_account=args.txaccount)

    # TODO unregister all plugins

    if not args.no_testcases:
        m.finalize()

