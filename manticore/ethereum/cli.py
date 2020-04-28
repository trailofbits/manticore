import sys
import logging
from .detectors import (
    Detector,
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
from .manticore import ManticoreEVM, set_verbosity
from .plugins import FilterFunctions, LoopDepthLimiter, VerboseTrace, KeepOnlyIfStorageChanges, SkipRevertBasicBlocks
from ..utils.nointerrupt import WithKeyboardInterruptAs
from ..utils import config, log

import argparse
from crytic_compile import is_supported, cryticparser

# Add crytic compile arguments
# See https://github.com/crytic/crytic-compile/wiki/Configuration
parser = argparse.ArgumentParser(formatter_class=argparse.ArgumentDefaultsHelpFormatter)
cryticparser.init(parser)
cc_flags = config.get_group("cc")
action_group = parser._action_groups[1]
for action in action_group._actions:
    if isinstance(action, (argparse._StoreAction, argparse._StoreTrueAction)):
        name = action.dest
        name.replace("_", "-")
        description = action.help
        description = description.replace("--", "--cc-")
        default = action.default
        if default is None:
            default = ""
        cc_flags.add(name, default, description=description)

cli_flags = config.get_group("cli")
cli_flags.add("profile", default=False, description="Enable worker profiling mode")

eth_flags = config.get_group("eth")
eth_flags.add(
    "explore_balance",
    default=False,
    description="Explore states in which only the balance was changed",
)

eth_flags.add(
    "verbose-trace", default=False, description="Dump an extra verbose trace for each state"
)
eth_flags.add(
    "txlimit",
    default=-1,
    description="Maximum number of symbolic transactions to run (-1 means unlimited)",
)

eth_flags.add("txnocoverage", default=False, description="Do not use coverage as stopping criteria")

eth_flags.add("txnoether", default=False, description="Do not attempt to send ether to contract")

eth_flags.add(
    "txaccount",
    default="attacker",
    description='Account used as caller in the symbolic transactions, either "attacker" or '
    '"owner" or "combo1" (uses both)',
)

eth_flags.add(
    "txpreconstrain",
    default=False,
    description="Constrain human transactions to avoid exceptions in the contract function dispatcher",
)

eth_flags.add(
    "contract", default="", description="Contract name to analyze in case of multiple contracts"
)

eth_flags.add("list-detectors", description="List available detectors", default=False)
eth_flags.add(
    "include-detectors",
    description="Comma-separated list of detectors that should be excluded (see --list-detectors)",
    default="",
)
eth_flags.add("include-all", description="Includes all detectors", default=False)

eth_flags.add(
    "avoid-constant",
    default=False,
    description="Avoid exploring constant functions for human transactions",
)

eth_flags.add(
    "limit-loops",
    default=False,
    description="Avoid exploring constant functions for human transactions",
)

eth_flags.add(
    "no-testcases",
    default=False,
    description="Do not generate testcases for discovered states when analysis finishes",
)

eth_flags.add(
    "only-alive-testcases",
    default=False,
    description="Do not generate testcases for invalid/throwing states when analysis finishes",
)

eth_flags.add(
    "quick-mode",
    default=False,
    description="Configure Manticore for quick exploration. Disable gas, generate testcase only for alive states, "
    "do not explore constant functions. Disable all detectors."
)

eth_flags.add(
    "skip_reverts",
    default=False,
    description="Simply avoid exploring basic blocks that end in a REVERT",
)


def get_detectors_classes():
    return [cls for cls in Detector.__subclasses__()]


def choose_detectors(eth_flags):
    # The RaceCondition detector has been disabled for now as it seems to collide with IntegerOverflow detector
    # FIXME
    included_detectors = eth_flags.include_detectors.split(",")
    if "race-condition" in included_detectors and "overflow" in included_detectors:
        raiseException(
            "The RaceCondition detector has been disabled for now as it seems to collide with IntegerOverflow detector, can not have race-condition and overflow at the same time."
        )
    for detector_cls in get_detectors_classes():
        if not eth_flags.include_all and detector_cls.ARGUMENT not in included_detectors:
            continue
        if eth_flags.include_all and "race-condition" == detector_cls.ARGUMENT:
            continue
        yield detector_cls


logger = logging.getLogger("manticoreEVM.main")


def ethereum_main():
    # Gets the default config constants/variables from their declarations
    cfg = config.get_default_config()
    # Build an argument parser out of the declared configuration
    # So user of CLI can override ALL config variables
    parser = cfg.prepare_argument_parser()
    # Add non conflicting application specific items: argv
    parser.add_argument(
        "argv",
        type=str,
        nargs="*",
        default=[],
        help="Path to program, and arguments ('+' in arguments indicates symbolic byte).",
    )

    # Parse the actual commandline
    args = parser.parse_args(sys.argv[1:])
    # Procces and ingest the overwrided values
    cfg.process_config_values(parser, args)

    # Application code starts
    if cfg["cli"].no_colors:
        log.disable_colors()
    sys.setrecursionlimit(cfg["cli"].recursionlimit)

    set_verbosity(cfg["cli"].verbosity)

    # Turn on other flags to make it quick
    if cfg["eth"].quick_mode:
        cfg["eth"].avoid_constant = True
        cfg["eth"].include_all = False
        cfg["eth"].only_alive_testcases = True
        cfg["evm"].oog = "ignore"
        cfg["evm"].skip_reverts = True

    if cfg["eth"].list_detectors:
        print("Detectors: ", ", ".join(detector.ARGUMENT for detector in get_detectors_classes()))

    m = ManticoreEVM(cfg=cfg)

    with WithKeyboardInterruptAs(m.kill):
        if cfg["eth"].skip_reverts:
            m.register_plugin(SkipRevertBasicBlocks())

        if cfg["eth"].explore_balance:
            m.register_plugin(KeepOnlyIfStorageChanges())

        if cfg["eth"].verbose_trace:
            m.register_plugin(VerboseTrace())

        if cfg["eth"].limit_loops:
            m.register_plugin(LoopDepthLimiter())

        for detector in choose_detectors(cfg["eth"]):
            m.register_detector(detector())

        if cli_flags.profile:
            profiler = Profiler()
            m.register_plugin(profiler)

        if cfg["eth"].avoid_constant:
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
                contract_name=cfg["eth"].contract,
                tx_limit=cfg["eth"].txlimit,
                tx_use_coverage=not cfg["eth"].txnocoverage,
                tx_send_ether=not cfg["eth"].txnoether,
                tx_account=cfg["eth"].txaccount,
                tx_preconstrain=cfg["eth"].txpreconstrain,
                compile_args=cfg["cc"],
            )

        if not cfg["eth"].no_testcases:
            m.finalize(only_alive_states=cfg["eth"].only_alive_testcases)
        else:
            m.kill()

        for detector in list(m.detectors):
            m.unregister_detector(detector)

        for plugin in list(m.plugins):
            m.unregister_plugin(plugin)
