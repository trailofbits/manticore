from manticore.seth import ManticoreEVM
################ Script #######################

seth = ManticoreEVM()
seth.verbosity(0)
#And now make the contract account to analyze
# cat  | solc --bin 
source_code = '''
pragma solidity ^0.4.13;

contract Test {
    event Log(string);

    function target() payable public {
        if (msg.value > 10)
            Log("Value greater than 10");
        else
            Log("Value less or equal than 10");

    } 

}
'''
#Initialize accounts
user_account = seth.create_account(balance=1000)  
contract_account = seth.solidity_create_contract(source_code, owner=user_account)


contract_account.target(value=seth.SValue)


print "[+] There are %d reverted states now"% len(seth.final_state_ids)
for state_id in seth.final_state_ids:
    seth.report(state_id)

print "[+] There are %d alive states now"% len(seth.running_state_ids)
for state_id in seth.running_state_ids:
    seth.report(state_id)

print "[+] Global coverage:"
print seth.coverage(contract_account)


