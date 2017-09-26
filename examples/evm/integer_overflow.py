from seth import *

seth = ManticoreEVM()

#And now make the contract account to analyze
source_code = '''
pragma solidity ^0.4.15;

contract Overflow {
    event Log(string);
    uint private sellerBalance=0;
    
    function add(uint value) returns (bool){
        sellerBalance += value; // complicated math with possible overflow

        // possible auditor assert
        assert(sellerBalance >= value); 
    } 
}
'''

#Initialize user and contracts
user_account = seth.create_account(balance=1000)
bytecode = seth.compile(source_code)
contract_account = seth.create_contract(owner=user_account, 
                                          balance=0, 
                                          init=bytecode)

#First add wont owerflow uint256 representation
symbolic_data = seth.make_function_call('add(uint256)', None)
seth.transaction(  caller=user_account,
                    address=contract_account,
                    value=0,
                    data=symbolic_data,
                 )

#Potential overflow
symbolic_data = seth.make_function_call('add(uint256)', None)
seth.transaction(  caller=user_account,
                    address=contract_account,
                    value=0,
                    data=symbolic_data
                 )


print "[+] There are %d reverted states now"% len(seth.final_state_ids)
for state_id in seth.final_state_ids:
    seth.report(state_id)

print "[+] There are %d alive states now"% len(seth.running_state_ids)
for state_id in seth.running_state_ids:
    seth.report(state_id)

print "[+] Global coverage: %x"% contract_account
print seth.coverage(contract_account)


