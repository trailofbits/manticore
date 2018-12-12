from .detectors import DetectInvalid, DetectIntegerOverflow, DetectUninitializedStorage, \
    DetectUninitializedMemory, DetectReentrancySimple, DetectReentrancyAdvanced, \
    DetectUnusedRetVal, DetectSuicidal, DetectDelegatecall, \
    DetectExternalCallAndLeak, DetectEnvInstruction, DetectRaceCondition, DetectorClassification
from .manticore import ManticoreEVM
from .plugins import FilterFunctions, LoopDepthLimiter, VerboseTrace


def get_detectors_classes():
    return [
        DetectInvalid, DetectIntegerOverflow, DetectUninitializedStorage, DetectUninitializedMemory,
        DetectReentrancySimple, DetectReentrancyAdvanced, DetectUnusedRetVal, DetectSuicidal, DetectDelegatecall,
        DetectExternalCallAndLeak, DetectEnvInstruction,
        # The RaceCondition detector has been disabled for now as it seems to collide with IntegerOverflow detector
        # DetectRaceCondition
    ]


def choose_detectors(args):
    all_detector_classes = get_detectors_classes()
    detectors = {d.ARGUMENT: d for d in all_detector_classes}
    arguments = list(detectors.keys())

    detectors_to_run = []

    if not args.exclude_all:
        exclude = []

        if args.detectors_to_exclude:
            exclude = args.detectors_to_exclude.split(',')

            for e in exclude:
                if e not in arguments:
                    raise Exception(f'{e} is not a detector name, must be one of {arguments}. See also `--list-detectors`.')

        for arg, detector_cls in detectors.items():
            if arg not in exclude:
                detectors_to_run.append(detector_cls)

    return detectors_to_run


def ethereum_main(args, logger):
    m = ManticoreEVM(procs=args.procs, workspace_url=args.workspace)

    if args.verbose_trace:
        m.register_plugin(VerboseTrace())

    if args.limit_loops:
        m.register_plugin(LoopDepthLimiter())

    for detector in choose_detectors(args):
        m.register_detector(detector())

    if args.avoid_constant:
        # avoid all human level tx that has no effect on the storage
        filter_nohuman_constants = FilterFunctions(regexp=r".*", depth='human', mutability='constant', include=False)
        m.register_plugin(filter_nohuman_constants)

    logger.info("Beginning analysis")

    with m.shutdown_timeout(args.timeout):
        m.multi_tx_analysis(args.argv[0], contract_name=args.contract, tx_limit=args.txlimit,
                            tx_use_coverage=not args.txnocoverage, tx_send_ether=not args.txnoether,
                            tx_account=args.txaccount, tx_preconstrain=args.txpreconstrain)

    if not args.no_testcases:
        m.finalize()

    for detector in list(m.detectors):
        m.unregister_detector(detector)

    for plugin in list(m.plugins):
        m.unregister_plugin(plugin)
