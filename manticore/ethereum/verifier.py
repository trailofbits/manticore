"""
$python manticore-verifier.py property.sol TestToken
"""
import re
import sys
from itertools import chain
from manticore.ethereum import ManticoreEVM
from manticore.ethereum.detectors import DetectIntegerOverflow
from manticore.ethereum.plugins import (FilterFunctions,VerboseTrace,KeepOnlyIfStorageChanges)
from manticore.core.smtlib.operators import OR
from manticore.ethereum.abi import ABI
from manticore.utils.log import set_verbosity
from prettytable import PrettyTable
from manticore.utils import config


def main():
    ################ Script #######################
    if len(sys.argv) != 3:
        print ("Usage:")
        print ("  ",sys.argv[0], "contract.sol", "ContractName")
        sys.exit()

    # Property STEM
    PROPRE = r"crytic_test_.*"

    ## Termination condition
    # Exploration will stop when some of the following happens:
    # * MAXTX human transaction sent
    # * Code coverage is greater than MAXCOV meassured on target contract
    # * No more coverage was gained in the last transaction
    # * At least MAXFAIL different properties where found to be breakable. (1 for fail fast)

    # Max transaction count to explore
    MAXTX=3
    # Max coverage % to get
    MAXCOV = 100
    # Max different properties fails
    MAXFAIL = None

    config.get_group("smt").timeout=120
    config.get_group("smt").memory=16384
    config.get_group("smt").optimize = False
    config.get_group("evm").oog = "ignore"


    # Main manticore manager object
    m = ManticoreEVM()
    # avoid all human level tx that are marked as constant (have no effect on the storage)
    filter_out_human_constants = FilterFunctions(
        regexp=r".*", depth="human", mutability="constant", include=False
    )
    m.register_plugin(filter_out_human_constants)
    filter_out_human_constants.disable()

    #Avoid automatically exploring property
    filter_no_crytic = FilterFunctions(
        regexp=PROPRE, include=False
    )
    m.register_plugin(filter_no_crytic)
    filter_no_crytic.disable()

    #Only explore properties (at human level)
    filter_only_crytic = FilterFunctions(
        regexp=PROPRE, depth="human", fallback=False, include=True
    )
    m.register_plugin(filter_only_crytic)
    filter_only_crytic.disable()

    # And now make the contract account to analyze
    source_code = sys.argv[1]

    #a legitimate user
    user_account = m.create_account(balance=10**10)
    #the address used for deployment
    owner_account = m.create_account(balance=10**10)
    #an attacker account 
    attacker_account = m.create_account(balance=10**10)
    #the target contract account
    contract_account = m.solidity_create_contract(source_code, owner=owner_account, contract_name=sys.argv[2])

    properties = {}
    md = m.get_metadata(contract_account)
    for func_hsh in md.function_selectors:
        func_name = md.get_abi(func_hsh)['name']
        if re.match(PROPRE, func_name):
            properties[func_name] = []
    MAXFAIL = len(properties) if MAXFAIL is None else MAXFAIL

    tx_num = 0 # transactions count 
    current_coverage = None #obtained coverge %

    print (f"Transaction {tx_num}. Ready: {m.count_ready_states()}, Terminated: {m.count_terminated_states()}")
    with m.kill_timeout(timeout=100):
        while True:
            #check if we found a way to break more than MAXFAIL properties
            broken_properties = (sum(int(len(x)!=0) for x in properties.values()))
            if broken_properties >= MAXFAIL:
                break

            #check if we sent more than MAXTX transaction
            if tx_num >= MAXTX:
                break
            tx_num += 1

            # check if we got enough coverage
            new_coverage = m.global_coverage(contract_account)
            if new_coverage >= MAXCOV:
                break

            # check if we have made coverage progress in the last transaction
            if current_coverage == new_coverage:
                break
            current_coverage = new_coverage

            # check if timeout was requested
            if m.is_killed():
                break

            # Explore all methods but the "crytic_" properties
            # Note: you may be tempted to get all valid function ids/hashes from the 
            #  metadata and to constrain the first 4 bytes of the calldata here.
            #  This wont work because we also want to prevent the contract to call 
            #  crytic added methods as internal transactions  
            filter_no_crytic.enable()               #filter out crytic_porperties
            filter_out_human_constants.enable()     #Exclude constant methods
            filter_only_crytic.disable()            #Exclude all methods that are not property checks

            symbolic_data = m.make_symbolic_buffer(320)
            symbolic_value = m.make_symbolic_value()
            caller_account = m.make_symbolic_value(160)
            m.constrain(OR(caller_account == attacker_account, caller_account == user_account))
            m.transaction(
                caller=caller_account, address=contract_account, value=symbolic_value, data=symbolic_data
            )

            m.clear_terminated_states() #no interest in reverted states
            m.take_snapshot() #make a copy of all ready states
            print (f"Transaction {tx_num}. Ready: {m.count_ready_states()}, Terminated: {m.count_terminated_states()}")

            #And now explore all properties (and only the properties)
            filter_no_crytic.disable()             #Allow crytic_porperties
            filter_out_human_constants.disable()   #Allow them to be marked as constants
            filter_only_crytic.enable()            #Exclude all methods that are not property checks
            symbolic_data = m.make_symbolic_buffer(4)
            m.transaction(
                caller=user_account, address=contract_account, value=0, data=symbolic_data
            )

            for state in m.all_states:            
                world = state.platform
                tx = world.human_transactions[-1]
                md = m.get_metadata(tx.address)

                for func_id in map(bytes, state.solve_n(tx.data[:4], nsolves=100)):
                    func_name = md.get_abi(func_id)['name']
                    if not func_name.endswith('revert'):
                        # Property does not ends in "revert"
                        # It must RETURN a 1
                        if tx.return_value == 1:
                            #TODO: test when property STOPs 
                            return_data = ABI.deserialize("bool", tx.return_data)
                            if state.can_be_true(return_data == 0):
                                with state as temp_state:
                                    temp_state.constrain(tx.data[:4] == func_id)
                                    temp_state.constrain(return_data == 0)
                                    testcase = m.generate_testcase(temp_state, f"property {md.get_func_name(func_id)} is broken")
                                    properties[func_name].append(testcase.num)
                            else:
                                pass #property passed
                        else:
                            # this kind of property must not REVERT
                            testcase = m.generate_testcase(temp_state, f"Some property is broken (REVERTED)")
                            properties[func_name].append(testcase.num)
                    else:
                        # property name ends in "revert" so it MUST revert
                        if tx.result != "REVERT":
                            testcase = m.generate_testcase(temp_state, f"Some property is broken did not reverted.(MUST REVERTED)")
                            properties[func_name].append(testcase.num)
                        else:
                            pass # property pass
     
            m.clear_terminated_states() #no interest in reverted states for now!
            m.goto_snapshot()

    m.clear_terminated_states()
    m.clear_snapshot()

        
    x = PrettyTable()
    x.field_names = ["Property Named", "Status"] 
    for name, testcases in sorted(properties.items()):
        result = "passed"
        if testcases:
            result = f"failed ({testcases[0]})"
        x.add_row((name, result))
    print (x)

    print (f"Checkout testcases here:{m.workspace}")


if __name__ == '__main__':
    main()
