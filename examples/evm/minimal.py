from manticore.seth import ManticoreEVM
################ Script #######################

seth = ManticoreEVM()
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

user_account = seth.create_account(balance=1000)
print "[+] Creating a user account", user_account

contract_account = seth.solidity_create_contract(source_code, owner=user_account)
print "[+] Creating a contract account", contract_account
print "[+] Source code:"
print source_code

print "[+] Now the symbolic values"
symbolic_data = seth.make_symbolic_buffer(320) 
symbolic_value = None 
seth.transaction(caller=user_account,
                address=contract_account,
                data=symbolic_data,
                value=symbolic_value )

#Let seth know we are not sending more transactions 
seth.finalize()
print "[+] Look for results in %s"% seth.workspace
