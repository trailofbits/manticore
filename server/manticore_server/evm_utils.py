import argparse
import shlex
from typing import List, Type

from crytic_compile import cryticparser
from manticore.core.plugin import Profiler
from manticore.ethereum import (
    DetectDelegatecall,
    DetectEnvInstruction,
    DetectExternalCallAndLeak,
    DetectIntegerOverflow,
    DetectInvalid,
    DetectManipulableBalance,
    Detector,
    DetectReentrancyAdvanced,
    DetectReentrancySimple,
    DetectSuicidal,
    DetectUninitializedMemory,
    DetectUninitializedStorage,
    DetectUnusedRetVal,
    ManticoreEVM,
)
from manticore.ethereum.plugins import (
    FilterFunctions,
    KeepOnlyIfStorageChanges,
    LoopDepthLimiter,
    SkipRevertBasicBlocks,
    VerboseTrace,
)
from manticore.utils import config


def get_detectors_classes() -> List[Type[Detector]]:
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


def parse_detectors(detectors_to_exclude: List[str]) -> List[Type[Detector]]:
    """returns a list of detectors that should be used"""
    all_detector_classes = get_detectors_classes()
    all_detector_args = map(lambda x: x.ARGUMENT, all_detector_classes)
    for d in detectors_to_exclude:
        if d not in all_detector_args:
            raise Exception(
                f"{d} is not a detector name, must be one of {list(all_detector_args)}. See also `--list-detectors`."
            )

    return [d for d in all_detector_classes if d.ARGUMENT not in detectors_to_exclude]


def setup_detectors_flags(
    detectors_to_exclude: List[str], additional_flags: str, m: ManticoreEVM
) -> argparse.Namespace:
    """parse and apply additional arguments for manticore EVM execution, CLI-style"""

    parser = argparse.ArgumentParser(
        description="Symbolic execution tool",
        prog="manticore",
        formatter_class=argparse.ArgumentDefaultsHelpFormatter,
    )

    consts = config.get_group("main")
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

    # Add crytic compile arguments
    # See https://github.com/crytic/crytic-compile/wiki/Configuration
    cryticparser.init(parser)

    eth_flags = parser.add_argument_group("Ethereum flags")

    eth_flags.add_argument(
        "--verbose-trace",
        action="store_true",
        help="Dump an extra verbose trace for each state",
    )

    eth_flags.add_argument(
        "--txnocoverage",
        action="store_true",
        help="Do not use coverage as stopping criteria",
    )

    eth_flags.add_argument(
        "--txnoether",
        action="store_true",
        help="Do not attempt to send ether to contract",
    )

    eth_flags.add_argument(
        "--txpreconstrain",
        action="store_true",
        help="Constrain human transactions to avoid exceptions in the contract function dispatcher",
    )

    eth_flags.add_argument(
        "--avoid-constant",
        action="store_true",
        help="Avoid exploring constant functions for human transactions",
    )

    eth_flags.add_argument(
        "--limit-loops",
        action="store_true",
        help="Limit loops depth",
    )

    eth_flags.add_argument(
        "--no-testcases",
        action="store_true",
        help="Do not generate testcases for discovered states when analysis finishes",
    )

    eth_flags.add_argument(
        "--only-alive-testcases",
        action="store_true",
        help="Do not generate testcases for invalid/throwing states when analysis finishes",
    )

    eth_flags.add_argument(
        "--thorough-mode",
        action="store_true",
        help="Configure Manticore for more exhaustive exploration. Evaluate gas, generate testcases for dead states, "
        "explore constant functions, and run a small suite of detectors.",
    )

    config_flags = parser.add_argument_group("Constants")
    config.add_config_vars_to_argparse(config_flags)

    args = parser.parse_args(shlex.split(additional_flags))
    config.process_config_values(parser, args)

    if not args.thorough_mode:
        args.avoid_constant = True
        args.exclude_all = True
        args.only_alive_testcases = True
        consts_evm = config.get_group("evm")
        consts_evm.oog = "ignore"
        consts.skip_reverts = True

    if consts.skip_reverts:
        m.register_plugin(SkipRevertBasicBlocks())

    if consts.explore_balance:
        m.register_plugin(KeepOnlyIfStorageChanges())

    if args.verbose_trace:
        m.register_plugin(VerboseTrace())

    if args.limit_loops:
        m.register_plugin(LoopDepthLimiter())

    for detector in parse_detectors(detectors_to_exclude):
        m.register_plugin(detector())

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
        print(f'Registered plugins: {", ".join(d.name for d in m.plugins.values())}')

    return args
