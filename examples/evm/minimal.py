from manticore.ethereum import ManticoreEVM, evm
################ Script #######################

m = ManticoreEVM()

#And now make the contract account to analyze
# cat  | solc --bin 
source_code = '''
pragma solidity ^0.4.13;
contract NoDistpatcher {
    event Log(string);

    function  named_func(uint x) returns (uint) {
    return 5 + x;
    }

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

user_account = m.create_account(balance=1000)
print("[+] Creating a user account", user_account)


contract_account = m.solidity_create_contract(source_code, owner=user_account)
print "[+] Creating a contract account", contract_account
contract_account.named_func(1)

print("[+] Now the symbolic values")
symbolic_data = m.make_symbolic_buffer(320) 
symbolic_value = None 
m.transaction(caller=user_account,
                address=contract_account,
                data=symbolic_data,
                value=symbolic_value )

#Let seth know we are not sending more transactions 
m.finalize()
print("[+] Look for results in {}".format(m.workspace))
