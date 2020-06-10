"""
$python manticore-verifier.py property.sol TestToken
"""
import re
import sys
import argparse
import logging
import pkg_resources
from itertools import chain
from manticore.ethereum import ManticoreEVM
from manticore.ethereum.detectors import DetectIntegerOverflow
from manticore.ethereum.plugins import FilterFunctions, VerboseTrace, KeepOnlyIfStorageChanges
from manticore.core.smtlib.operators import OR
from manticore.ethereum.abi import ABI
from manticore.utils.log import set_verbosity
from prettytable import PrettyTable
from manticore.utils import config
from manticore.utils.nointerrupt import WithKeyboardInterruptAs

consts = config.get_group("cli")
consts.add(
    "config", default="config.yaml", description="Configure user for solidity property verif",
)


def manticore_verifier(
    source_code,
    contract_name,
    maxfail=None,
    maxt=3,
    maxcov=100,
    deployer=None,
    senders=(None,),
    psender=None,
    propre=r"crytic_test_.*",
    compile_args=None,
    outputspace_url=None,
):
    """ Verify solidity properties
    The results are dumped to stdout and to the workspace folder.

        $manticore_verifier tests/ethereum/contracts/prop_verifier.sol TestToken
        Transaction 0. Ready: 1, Terminated: 0
        Transaction 1. Ready: 4, Terminated: 0
        +---------------------+------------+
        |    Property Named   |   Status   |
        +---------------------+------------+
        | crytic_test_balance | failed (0) |
        +---------------------+------------+
        Checkout testcases here:./mcore_ca_gjpqw

    :param maxfail: stop after maxfail properties are failing. All if None
    :param maxcov: Stop after maxcov % coverage is obtained in the main contract
    :param maxt: Max transaction count to explore
    :param deployer: (optional) address of account used to deploy the contract
    :param senders: (optional) a list of calles addresses for the exploration
    :param psender: (optional) address from where the property is tested
    :param source_code: A filename or source code
    :param contract_name: The target contract name defined in the source code
    :param propre: A regular expression for selecting properties
    :param outputspace_url: where to put the extended result
    :return:
    """
    # Termination condition
    # Exploration will stop when some of the following happens:
    # * MAXTX human transaction sent
    # * Code coverage is greater than MAXCOV meassured on target contract
    # * No more coverage was gained in the last transaction
    # * At least MAXFAIL different properties where found to be breakable. (1 for fail fast)

    # Max transaction count to explore
    MAXTX = maxt
    # Max coverage % to get
    MAXCOV = maxcov
    # Max different properties fails
    MAXFAIL = maxfail

    config.get_group("smt").timeout = 120
    config.get_group("smt").memory = 16384
    config.get_group("smt").optimize = False
    config.get_group("evm").oog = "ignore"

    print(
        f"""
# Exploration will stop when some of the following happens:
# * {MAXTX} human transaction sent
# * Code coverage is greater than {MAXCOV}% meassured on target contract
# * No more coverage was gained in the last transaction
# * At least {MAXFAIL} different properties where found to be breakable. (1 for fail fast)
"""
    )
    # Main manticore manager object
    m = ManticoreEVM()
    # avoid all human level tx that are marked as constant (have no effect on the storage)
    filter_out_human_constants = FilterFunctions(
        regexp=r".*", depth="human", mutability="constant", include=False
    )
    m.register_plugin(filter_out_human_constants)
    filter_out_human_constants.disable()

    # Avoid automatically exploring property
    filter_no_crytic = FilterFunctions(regexp=propre, include=False)
    m.register_plugin(filter_no_crytic)
    filter_no_crytic.disable()

    # Only explore properties (at human level)
    filter_only_crytic = FilterFunctions(regexp=propre, depth="human", fallback=False, include=True)
    m.register_plugin(filter_only_crytic)
    filter_only_crytic.disable()

    # And now make the contract account to analyze

    # User accounts. Transactions trying to break the property are send from one
    # of this
    user_accounts = []
    for address_i in senders:
        user_accounts.append(m.create_account(balance=10 ** 10, address=address_i))
    # the address used for deployment
    owner_account = m.create_account(balance=10 ** 10, address=deployer)
    # the target contract account
    contract_account = m.solidity_create_contract(
        source_code, owner=owner_account, contract_name=contract_name, compile_args=compile_args,
    )
    # the address used for checking porperties
    checker_account = m.create_account(balance=10 ** 10, address=psender)

    properties = {}
    md = m.get_metadata(contract_account)
    for func_hsh in md.function_selectors:
        func_name = md.get_abi(func_hsh)["name"]
        if re.match(propre, func_name):
            properties[func_name] = []
    MAXFAIL = len(properties) if MAXFAIL is None else MAXFAIL

    tx_num = 0  # transactions count
    current_coverage = None  # obtained coverge %

    print(
        f"Transaction {tx_num}. Ready: {m.count_ready_states()}, Terminated: {m.count_terminated_states()}"
    )
    with m.kill_timeout(timeout=100):
        while True:
            # check if we found a way to break more than MAXFAIL properties
            broken_properties = sum(int(len(x) != 0) for x in properties.values())
            if broken_properties >= MAXFAIL:
                print(
                    f"Found {broken_properties}/{len(properties)} failing properties. Stopping exploraiton."
                )
                break

            # check if we sent more than MAXTX transaction
            if tx_num >= MAXTX:
                print("Max numbr of transactions reached({tx_num})")
                break
            tx_num += 1

            # check if we got enough coverage
            new_coverage = m.global_coverage(contract_account)
            if new_coverage >= MAXCOV:
                print(
                    "Current coverage({new_coverage}%) is greater than max allowed({MAXCOV}%).Stopping exploraiton."
                )
                break

            # check if we have made coverage progress in the last transaction
            if current_coverage == new_coverage:
                print(f"No coverage progress. Stalled at {new_coverage}%. Stopping exploraiton.")
                break
            current_coverage = new_coverage

            # check if timeout was requested
            if m.is_killed():
                print("Cancelled or timeout.")
                break

            # Explore all methods but the "crytic_" properties
            # Note: you may be tempted to get all valid function ids/hashes from the
            #  metadata and to constrain the first 4 bytes of the calldata here.
            #  This wont work because we also want to prevent the contract to call
            #  crytic added methods as internal transactions
            filter_no_crytic.enable()  # filter out crytic_porperties
            filter_out_human_constants.enable()  # Exclude constant methods
            filter_only_crytic.disable()  # Exclude all methods that are not property checks

            symbolic_data = m.make_symbolic_buffer(320)
            symbolic_value = m.make_symbolic_value()
            caller_account = m.make_symbolic_value(160)
            args = tuple((caller_account == address_i for address_i in user_accounts))
            m.constrain(OR(*args, True))
            m.transaction(
                caller=caller_account,
                address=contract_account,
                value=symbolic_value,
                data=symbolic_data,
            )

            m.clear_terminated_states()  # no interest in reverted states
            m.take_snapshot()  # make a copy of all ready states
            print(
                f"Transaction {tx_num}. Ready: {m.count_ready_states()}, Terminated: {m.count_terminated_states()}"
            )

            # And now explore all properties (and only the properties)
            filter_no_crytic.disable()  # Allow crytic_porperties
            filter_out_human_constants.disable()  # Allow them to be marked as constants
            filter_only_crytic.enable()  # Exclude all methods that are not property checks
            symbolic_data = m.make_symbolic_buffer(4)
            m.transaction(
                caller=checker_account, address=contract_account, value=0, data=symbolic_data
            )

            for state in m.all_states:
                world = state.platform
                tx = world.human_transactions[-1]
                md = m.get_metadata(tx.address)

                for func_id in map(bytes, state.solve_n(tx.data[:4], nsolves=100)):
                    func_name = md.get_abi(func_id)["name"]
                    if not func_name.endswith("revert"):
                        # Property does not ends in "revert"
                        # It must RETURN a 1
                        if tx.return_value == 1:
                            # TODO: test when property STOPs
                            return_data = ABI.deserialize("bool", tx.return_data)
                            if state.can_be_true(return_data == 0):
                                with state as temp_state:
                                    temp_state.constrain(tx.data[:4] == func_id)
                                    temp_state.constrain(return_data == 0)
                                    testcase = m.generate_testcase(
                                        temp_state,
                                        f"property {md.get_func_name(func_id)} is broken",
                                    )
                                    properties[func_name].append(testcase.num)
                            else:
                                pass  # property passed
                        else:
                            # this kind of property must not REVERT
                            testcase = m.generate_testcase(
                                temp_state, f"Some property is broken (REVERTED)"
                            )
                            properties[func_name].append(testcase.num)
                    else:
                        # property name ends in "revert" so it MUST revert
                        if tx.result != "REVERT":
                            testcase = m.generate_testcase(
                                temp_state,
                                f"Some property is broken did not reverted.(MUST REVERTED)",
                            )
                            properties[func_name].append(testcase.num)
                        else:
                            pass  # property pass

            m.clear_terminated_states()  # no interest in reverted states for now!
            m.goto_snapshot()

    m.clear_terminated_states()
    m.clear_snapshot()

    if m.is_killed():
        print("Exploration ended by CTRL+C or timeout")

    print(f"{m.global_coverage(contract_account):3.2f}% EVM code covered ")

    x = PrettyTable()
    x.field_names = ["Property Named", "Status"]
    for name, testcases in sorted(properties.items()):
        result = "passed"
        if testcases:
            result = f"failed ({testcases[0]})"
        x.add_row((name, result))
    print(x)

    m.clear_ready_states()
    print(f"Checkout testcases here:{m.workspace}")


"""
config.yaml
deployer: "0x.."
sender: ["0x.."]
psender: "0x..."
deployer: who deploys the contract
sender: who calls the transactions (potentially can be multiple users)
psender: who calls the property
"""


def main():
    from crytic_compile import is_supported, cryticparser

    parser = argparse.ArgumentParser(
        description="Solidity property verifier",
        prog="manticore_verifier",
        formatter_class=argparse.ArgumentDefaultsHelpFormatter,
    )

    # Add crytic compile arguments
    # See https://github.com/crytic/crytic-compile/wiki/Configuration
    cryticparser.init(parser)

    parser.add_argument(
        "source_code", type=str, nargs="*", default=[], help="Contract source code",
    )
    parser.add_argument(
        "-v", action="count", default=0, help="Specify verbosity level from -v to -vvvv"
    )

    parser.add_argument(
        "--workspace",
        type=str,
        default=None,
        help=("A folder name for temporaries and results." "(default mcore_?????)"),
    )

    current_version = pkg_resources.get_distribution("manticore").version
    parser.add_argument(
        "--version",
        action="version",
        version=f"Manticore {current_version}",
        help="Show program version information",
    )
    parser.add_argument(
        "--config", type=str, help="Solisity property accounts config file (.yml)",
    )
    eth_flags = parser.add_argument_group("Ethereum flags")

    eth_flags.add_argument(
        "--txlimit",
        type=int,
        help="Maximum number of symbolic transactions to run (positive integer)",
    )

    eth_flags.add_argument(
        "--quick-mode",
        action="store_true",
        help="Configure Manticore for quick exploration. Disable gas, generate testcase only for alive states, "
        "do not explore constant functions. Disable all detectors.",
    )
    eth_flags.add_argument(
        "--contract_name", type=str, help="The target contract name defined in the source code"
    )
    eth_flags.add_argument(
        "--maxfail", type=int, help="stop after maxfail properties are failing. All if None"
    )
    eth_flags.add_argument(
        "--maxcov",
        type=int,
        default=100,
        help=" Stop after maxcov % coverage is obtained in the main contract",
    )
    eth_flags.add_argument("--maxt", type=int, default=3, help="Max transaction count to explore")
    eth_flags.add_argument(
        "--deployer", type=str, help="(optional) address of account used to deploy the contract"
    )
    eth_flags.add_argument(
        "--senders", type=str, help="(optional) a list of calles addresses for the exploration"
    )
    eth_flags.add_argument(
        "--checker", type=str, help="(optional) address from where the property is tested"
    )
    eth_flags.add_argument(
        "--propre", type=str, help="A regular expression for selecting properties"
    )
    eth_flags.add_argument("--outputspace_url", type=str, help="where to put the extended result")

    config_flags = parser.add_argument_group("Constants")
    config.add_config_vars_to_argparse(config_flags)

    parsed = parser.parse_args(sys.argv[1:])
    config.process_config_values(parser, parsed)

    if not parsed.source_code:
        print(parser.format_usage() + "error: the following arguments are required: contract")
        sys.exit(1)
    args = parsed
    set_verbosity(args.v)
    logger = logging.getLogger("manticore.main")

    source_code = args.source_code[0]
    contract_name = args.contract_name
    maxfail = args.maxfail
    maxt = args.maxt
    maxcov = args.maxcov
    return manticore_verifier(source_code, contract_name, maxfail=maxfail, maxt=maxt, maxcov=100)