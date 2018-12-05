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
        DetectExternalCallAndLeak, DetectEnvInstruction, DetectRaceCondition
    ]


def choose_detectors(args):
    all_detector_classes = get_detectors_classes()
    detectors = {d.ARGUMENT: d for d in all_detector_classes}

    detectors_to_run = []

    if args.detectors_to_run == 'all':
        detectors_to_run = all_detector_classes
        detectors_excluded = args.detectors_to_exclude.split(',')
        for d in detectors:
            if d in detectors_excluded:
                detectors_to_run.remove(detectors[d])
    else:
        for d in args.detectors_to_run.split(','):
            if d in detectors:
                detectors_to_run.append(detectors[d])
            else:
                raise Exception('Error: {} is not a detector'.format(d))
        return detectors_to_run

    if args.exclude_informational:
        detectors_to_run = [d for d in detectors_to_run if
                            d.IMPACT != DetectorClassification.INFORMATIONAL]
    if args.exclude_low:
        detectors_to_run = [d for d in detectors_to_run if
                            d.IMPACT != DetectorClassification.LOW]
    if args.exclude_medium:
        detectors_to_run = [d for d in detectors_to_run if
                            d.IMPACT != DetectorClassification.MEDIUM]
    if args.exclude_high:
        detectors_to_run = [d for d in detectors_to_run if
                            d.IMPACT != DetectorClassification.HIGH]
    if args.detectors_to_exclude:
        detectors_to_run = [d for d in detectors_to_run if
                            d.ARGUMENT not in args.detectors_to_exclude]

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
        m.multi_tx_analysis(args.argv[0], contract_name=args.contract, tx_limit=args.txlimit, tx_use_coverage=not args.txnocoverage, tx_send_ether=not args.txnoether, tx_account=args.txaccount)

    for detector in list(m.detectors):
        m.unregister_detector(detector)

    for plugin in list(m.plugins):
        m.unregister_plugin(plugin)

    if not args.no_testcases:
        m.finalize()
