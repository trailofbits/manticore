"""
$python manticore-verifier.py property.sol TestToken
"""
import os
import re
import sys
import argparse
import logging
import pkg_resources
from itertools import chain
from manticore.ethereum import ManticoreEVM
from manticore.ethereum.detectors import DetectIntegerOverflow
from manticore.ethereum.plugins import FilterFunctions, VerboseTrace, KeepOnlyIfStorageChanges
from manticore.core.smtlib.operators import OR, NOT, AND
from manticore.ethereum.abi import ABI
from manticore.utils.log import set_verbosity
from prettytable import PrettyTable
from manticore.utils import config
from manticore.utils.nointerrupt import WithKeyboardInterruptAs


def constrain_to_known_func_ids(state):
    world = state.platform
    tx = world.human_transactions[-1]
    md = state.manticore.get_metadata(tx.address)

    N = 0
    is_normal = False
    func_id = tx.data[:4]
    for func_hsh in md.function_selectors:
        N += 1
        is_normal = OR(func_hsh == func_id, is_normal)
    is_fallback = NOT(is_normal)
    is_known_func_id = is_normal

    chosen_fallback_func_is = None
    if state.can_be_true(is_fallback):
        with state as temp_state:
            temp_state.constraint(is_fallback)
            chosen_fallback_func_id = bytes(state.solve_one(tx.data[:4]))
            is_known_func_id = OR(is_known_func_id, chosen_fallback_func_id == func_id)
            N += 1
    state.constrain(is_known_func_id)
    return N


def manticore_verifier(
    source_code,
    contract_name,
    maxfail=None,
    maxt=3,
    maxcov=100,
    deployer=None,
    senders=None,
    psender=None,
    propre=r"crytic_.*",
    compile_args=None,
    outputspace_url=None,
    timeout=100,
):
    """Verify solidity properties
    The results are dumped to stdout and to the workspace folder.

        $manticore-verifier property.sol  --contract TestToken --smt.solver yices --maxt 4
        # Owner account: 0xf3c67ffb8ab4cdd4d3243ad247d0641cd24af939
        # Contract account: 0x6f4b51ac2eb017600e9263085cfa06f831132c72
        # Sender_0 account: 0x97528a0c7c6592772231fd581e5b42125c1a2ff4
        # PSender account: 0x97528a0c7c6592772231fd581e5b42125c1a2ff4
        # Found 2 properties: crytic_test_must_revert, crytic_test_balance
        # Exploration will stop when some of the following happens:
        # * 4 human transaction sent
        # * Code coverage is greater than 100% meassured on target contract
        # * No more coverage was gained in the last transaction
        # * At least 2 different properties where found to be breakable. (1 for fail fast)
        # * 240 seconds pass
        # Starting exploration...
        Transactions done: 0. States: 1, RT Coverage: 0.0%, Failing properties: 0/2
        Transactions done: 1. States: 2, RT Coverage: 55.43%, Failing properties: 0/2
        Transactions done: 2. States: 8, RT Coverage: 80.48%, Failing properties: 1/2
        Transactions done: 3. States: 30, RT Coverage: 80.48%, Failing properties: 1/2
        No coverage progress. Stopping exploration.
        Coverage obtained 80.48%. (RT + prop)
        +-------------------------+------------+
        |      Property Named     |   Status   |
        +-------------------------+------------+
        |   crytic_test_balance   | failed (0) |
        | crytic_test_must_revert |   passed   |
        +-------------------------+------------+
        Checkout testcases here:./mcore_6jdil7nh

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
    :param timeout: timeout in seconds
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
    config.get_group("evm").ignore_balance = True
    config.get_group("evm").oog = "ignore"

    print("# Welcome to manticore-verifier")
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
    senders = (None,) if senders is None else senders

    user_accounts = []
    for n, address_i in enumerate(senders):
        user_accounts.append(
            m.create_account(balance=10 ** 10, address=address_i, name=f"sender_{n}")
        )
    # the address used for deployment
    owner_account = m.create_account(balance=10 ** 10, address=deployer, name="deployer")
    # the target contract account
    contract_account = m.solidity_create_contract(
        source_code,
        owner=owner_account,
        contract_name=contract_name,
        compile_args=compile_args,
        name="contract_account",
    )
    # the address used for checking porperties
    checker_account = m.create_account(balance=10 ** 10, address=psender, name="psender")

    print(f"# Owner account: 0x{int(owner_account):x}")
    print(f"# Contract account: 0x{int(contract_account):x}")
    for n, user_account in enumerate(user_accounts):
        print(f"# Sender_{n} account: 0x{int(user_account):x}")
    print(f"# PSender account: 0x{int(checker_account):x}")

    properties = {}
    md = m.get_metadata(contract_account)
    for func_hsh in md.function_selectors:
        func_name = md.get_abi(func_hsh)["name"]
        if re.match(propre, func_name):
            properties[func_name] = []

    print(f"# Found {len(properties)} properties: {', '.join(properties.keys())}")
    if not properties:
        print("I am sorry I had to run the init bytecode for this.\n" "Good Bye.")
        return
    MAXFAIL = len(properties) if MAXFAIL is None else MAXFAIL
    tx_num = 0  # transactions count
    current_coverage = None  # obtained coverge %
    new_coverage = 0.0

    print(
        f"""# Exploration will stop when some of the following happens:
# * {MAXTX} human transaction sent
# * Code coverage is greater than {MAXCOV}% meassured on target contract
# * No more coverage was gained in the last transaction
# * At least {MAXFAIL} different properties where found to be breakable. (1 for fail fast)
# * {timeout} seconds pass"""
    )
    print("# Starting exploration...")
    print(
        f"Transactions done: {tx_num}. States: {m.count_ready_states()}, RT Coverage: {0.00}%, "
        f"Failing properties: 0/{len(properties)}"
    )
    with m.kill_timeout(timeout=timeout):
        while not m.is_killed():
            # check if we found a way to break more than MAXFAIL properties
            broken_properties = sum(int(len(x) != 0) for x in properties.values())
            if broken_properties >= MAXFAIL:
                print(
                    f"Found {broken_properties}/{len(properties)} failing properties. Stopping exploration."
                )
                break

            # check if we sent more than MAXTX transaction
            if tx_num >= MAXTX:
                print(f"Max number of transactions reached ({tx_num})")
                break
            tx_num += 1

            # check if we got enough coverage
            new_coverage = m.global_coverage(contract_account)
            if new_coverage >= MAXCOV:
                print(
                    f"Current coverage({new_coverage}%) is greater than max allowed ({MAXCOV}%). Stopping exploration."
                )
                break

            # check if we have made coverage progress in the last transaction
            if current_coverage == new_coverage:
                print(f"No coverage progress. Stopping exploration.")
                break
            current_coverage = new_coverage

            # Make sure we didn't time out before starting first transaction
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

            m.constrain(OR(*args, False))
            m.transaction(
                caller=caller_account,
                address=contract_account,
                value=symbolic_value,
                data=symbolic_data,
            )

            # check if timeout was requested during the previous transaction
            if m.is_killed():
                print("Cancelled or timeout.")
                break

            m.clear_terminated_states()  # no interest in reverted states
            m.take_snapshot()  # make a copy of all ready states
            print(
                f"Transactions done: {tx_num}. States: {m.count_ready_states()}, "
                f"RT Coverage: {m.global_coverage(contract_account):3.2f}%, "
                f"Failing properties: {broken_properties}/{len(properties)}"
            )

            # check if timeout was requested while we were taking the snapshot
            if m.is_killed():
                print("Cancelled or timeout.")
                break

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
                """
                A is _broken_ if:
                     * is normal property
                     * RETURN False
                   OR:
                     * property name ends with 'revert'
                     * does not REVERT
                Property is considered to _pass_ otherwise
                """
                N = constrain_to_known_func_ids(state)
                for func_id in map(bytes, state.solve_n(tx.data[:4], nsolves=N)):
                    func_name = md.get_abi(func_id)["name"]
                    if not func_name.endswith("revert"):
                        # Property does not ends in "revert"
                        # It must RETURN a 1
                        if tx.return_value == 1:
                            # TODO: test when property STOPs
                            return_data = ABI.deserialize("bool", tx.return_data)
                            testcase = m.generate_testcase(
                                state,
                                f"property {md.get_func_name(func_id)} is broken",
                                only_if=AND(tx.data[:4] == func_id, return_data == 0),
                            )
                            if testcase:
                                properties[func_name].append(testcase.num)
                    else:
                        # property name ends in "revert" so it MUST revert
                        if tx.result != "REVERT":
                            testcase = m.generate_testcase(
                                state,
                                f"Some property is broken did not reverted.(MUST REVERTED)",
                                only_if=tx.data[:4] == func_id,
                            )
                            if testcase:
                                properties[func_name].append(testcase.num)

            m.clear_terminated_states()  # no interest in reverted states for now!
            m.goto_snapshot()
        else:
            print("Cancelled or timeout.")

    m.clear_terminated_states()
    m.clear_ready_states()
    m.clear_snapshot()

    if m.is_killed():
        print("Exploration ended by CTRL+C or timeout")

    print(f"Coverage obtained {new_coverage:3.2f}%. (RT + prop)")

    x = PrettyTable()
    x.field_names = ["Property Named", "Status"]
    for name, testcases in sorted(properties.items()):
        result = "passed"
        if testcases:
            result = f"failed ({testcases[0]})"
        x.add_row((name, result))
    print(x)

    m.clear_ready_states()

    workspace = os.path.abspath(m.workspace)[len(os.getcwd()) + 1 :]
    print(f"Checkout testcases here:./{workspace}")


def main():
    from crytic_compile import is_supported, cryticparser

    parser = argparse.ArgumentParser(
        description="Solidity property verifier",
        prog="manticore_verifier",
        # formatter_class=argparse.ArgumentDefaultsHelpFormatter,
    )

    # Add crytic compile arguments
    # See https://github.com/crytic/crytic-compile/wiki/Configuration
    cryticparser.init(parser)

    parser.add_argument(
        "source_code",
        type=str,
        nargs="*",
        default=[],
        help="Contract source code",
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
        "--propconfig",
        type=str,
        help="Solidity property accounts config file (.yml)",
    )
    eth_flags = parser.add_argument_group("Ethereum flags")

    eth_flags.add_argument(
        "--thorough-mode",
        action="store_true",
        help="Configure Manticore for more exhaustive exploration. Evaluate gas, generate testcases for dead states, "
        "explore constant functions, and run a small suite of detectors.",
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
        help=" Stop after maxcov %% coverage is obtained in the main contract",
    )
    eth_flags.add_argument("--maxt", type=int, default=3, help="Max transaction count to explore")
    eth_flags.add_argument(
        "--deployer", type=str, help="(optional) address of account used to deploy the contract"
    )
    eth_flags.add_argument(
        "--senders",
        type=str,
        help="(optional) a comma separated list of sender addresses. The properties are going to be tested sending transactions from these addresses.",
    )
    eth_flags.add_argument(
        "--psender", type=str, help="(optional) address from where the property is tested"
    )
    eth_flags.add_argument(
        "--propre",
        default=r"crytic_.*",
        type=str,
        help="A regular expression for selecting properties",
    )
    eth_flags.add_argument(
        "--timeout", default=240, type=int, help="Exploration timeout in seconds"
    )
    eth_flags.add_argument("--outputspace_url", type=str, help="where to put the extended result")

    config_flags = parser.add_argument_group("Constants")
    config.add_config_vars_to_argparse(config_flags)

    parsed = parser.parse_args(sys.argv[1:])
    config.process_config_values(parser, parsed)

    if not parsed.source_code:
        print(parser.format_usage() + "error: You need to provide a contract source code.")
        sys.exit(1)
    args = parsed
    set_verbosity(args.v)
    logger = logging.getLogger("manticore.main")

    # read yaml config file
    deployer = None
    senders = None
    psenders = None
    if args.propconfig:
        """
        deployer: "0x41414141414141414141"  #who deploys the contract
        sender: ["0x51515151515151515151", "0x52525252525252525252"] #who calls the transactions (potentially can be multiple users)
        psender: "0x616161616161616161" #who calls the property
        """
        import yaml

        with open(args.propconfig) as f:
            c = yaml.safe_load(f)
            deployer = c.get("deployer")
            if deployer is not None:
                deployer = int(deployer, 0)

            senders = c.get("sender")
            if senders is not None:
                senders = [int(sender, 0) for sender in senders]

            psender = c.get("psender")
            if psender is not None:
                psender = int(psender, 0)

    # override with commandline args
    deployer = None
    if args.deployer is not None:
        deployer = int(args.deployer, 0)

    senders = None
    if args.senders is not None:
        senders = [int(sender, 0) for sender in args.senders.split(",")]

    psender = None
    if args.psender is not None:
        psender = int(args.psender, 0)

    source_code = args.source_code[0]
    contract_name = args.contract_name
    maxfail = args.maxfail
    maxt = args.maxt
    maxcov = args.maxcov
    return manticore_verifier(
        source_code,
        contract_name,
        maxfail=maxfail,
        maxt=maxt,
        maxcov=100,
        senders=senders,
        deployer=deployer,
        psender=psender,
        timeout=args.timeout,
        propre=args.propre,
        compile_args=vars(parsed),
    )
