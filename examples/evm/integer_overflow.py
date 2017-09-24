from seth1 import *
################ Script #######################

seth = SEthereum()
seth.verbosity(0)
#And now make the contract account to analyze
source_code = '''
pragma solidity ^0.4.15;

contract Overflow {
    uint private sellerBalance=0;
    
    function add(uint value) returns (bool){
        sellerBalance += value; // complicated math with possible overflow

        // possible auditor assert
        assert(sellerBalance >= value); 
    } 
}
'''

user_account = seth.create_account(balance=1000)

bytecode = seth.compile(source_code)
#Initialize contract
contract_account = seth.create_contract(owner=user_account, 
                                          balance=0, 
                                          init_bytecode=bytecode)

symbolic_data = seth.new_symbolic_buffer(name='msg.data.tx1', nbytes=38)
seth.transaction(  caller=user_account,
                    address=contract_account,
                    value=0,
                    data=symbolic_data,
                 )


symbolic_data = seth.new_symbolic_buffer(name='msg.data.tx2', nbytes=38)
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

print "[+] Global coverage:"
print seth.coverage(contract_account)


