from .detectors import (
    DetectInvalid,
    DetectIntegerOverflow,
    DetectUninitializedStorage,
    DetectUninitializedMemory,
    DetectReentrancySimple,
    DetectReentrancyAdvanced,
    DetectUnusedRetVal,
    DetectSuicidal,
    DetectDelegatecall,
    DetectExternalCallAndLeak,
    DetectEnvInstruction,
    DetectRaceCondition,
    DetectorClassification,
    DetectManipulableBalance,
)
from ..core.plugin import Profiler
from .manticore import ManticoreEVM
from .plugins import (
    FilterFunctions,
    LoopDepthLimiter,
    VerboseTrace,
    KeepOnlyIfStorageChanges,
    SkipRevertBasicBlocks,
)
from ..utils.nointerrupt import WithKeyboardInterruptAs
from ..utils import config

consts = config.get_group("cli")
consts.add("profile", default=False, description="Enable worker profiling mode")
consts.add(
    "explore_balance",
    default=False,
    description="Explore states in which only the balance was changed",
)

consts.add(
    "skip_reverts",
    default=False,
    description="Simply avoid exploring basic blocks that end in a REVERT",
)


def get_detectors_classes():
    return [
        DetectInvalid,
        DetectIntegerOverflow,
        DetectUninitializedStorage,
        DetectUninitializedMemory,
        DetectReentrancySimple,
        DetectReentrancyAdvanced,
        DetectUnusedRetVal,
        DetectSuicidal,
        DetectDelegatecall,
        DetectExternalCallAndLeak,
        DetectEnvInstruction,
        DetectManipulableBalance,
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
            exclude = args.detectors_to_exclude.split(",")

            for e in exclude:
                if e not in arguments:
                    raise Exception(
                        f"{e} is not a detector name, must be one of {arguments}. See also `--list-detectors`."
                    )

        for arg, detector_cls in detectors.items():
            if arg not in exclude:
                detectors_to_run.append(detector_cls)

    return detectors_to_run


def ethereum_main(args, logger):
    m = ManticoreEVM(workspace_url=args.workspace)

    if args.quick_mode:
        args.avoid_constant = True
        args.exclude_all = True
        args.only_alive_testcases = True
        consts_evm = config.get_group("evm")
        consts_evm.oog = "ignore"
        consts.skip_reverts = True

    with WithKeyboardInterruptAs(m.kill):
        if consts.skip_reverts:
            m.register_plugin(SkipRevertBasicBlocks())

        if consts.explore_balance:
            m.register_plugin(KeepOnlyIfStorageChanges())

        if args.verbose_trace:
            m.register_plugin(VerboseTrace())

        if args.limit_loops:
            m.register_plugin(LoopDepthLimiter())

        for detector in choose_detectors(args):
            m.register_detector(detector())

        if consts.profile:
            profiler = Profiler()
            m.register_plugin(profiler)

        if args.avoid_constant:
            # avoid all human level tx that has no effect on the storage
            filter_nohuman_constants = FilterFunctions(
                regexp=r".*", depth="human", mutability="constant", include=False
            )
            m.register_plugin(filter_nohuman_constants)

        if m.plugins:
            logger.info(f'Registered plugins: {", ".join(d.name for d in m.plugins)}')

        logger.info("Beginning analysis")

        with m.kill_timeout():
            m.multi_tx_analysis(
                args.argv[0],
                contract_name=args.contract,
                tx_limit=args.txlimit,
                tx_use_coverage=not args.txnocoverage,
                tx_send_ether=not args.txnoether,
                tx_account=args.txaccount,
                tx_preconstrain=args.txpreconstrain,
                compile_args=vars(args),  # FIXME
            )

        if not args.no_testcases:
            m.finalize(only_alive_states=args.only_alive_testcases)
        else:
            m.kill()

        for detector in list(m.detectors):
            m.unregister_detector(detector)

        for plugin in list(m.plugins):
            m.unregister_plugin(plugin)
