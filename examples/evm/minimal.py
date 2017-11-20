from seth import ManticoreEVM
################ Script #######################

seth = ManticoreEVM()
seth.verbosity(0)
#And now make the contract account to analyze
# cat  | solc --bin 
source_code = '''
pragma solidity ^0.4.13;
contract NoDistpatcher {
    event Log(string);

    function() payable {
        if (msg.data[0] == 'A') {
            Log("Got an A");
        }
        else{
            Log("Got something else");
        }
    } 
}
'''

print "[+] Creating a user account"
user_account = seth.create_account(balance=1000)


print "[+] Creating a contract account"
contract_account = seth.solidity_create_contract(source_code, owner=user_account)


print "[+] Now the symbolic values"

symbolic_data = seth.SByte(320) 
symbolic_value = None 
seth.transaction(caller=user_account,
                address=contract_account,
                data=symbolic_data,
                value=symbolic_value )

print "[+] There are %d reverted states now"% len(seth.final_state_ids)

print "[+] There are %d alive states now"% len(seth.running_state_ids)
for state_id in seth.running_state_ids:
    seth.report(state_id)

print "[+] Global coverage:"
print seth.coverage(contract_account)



