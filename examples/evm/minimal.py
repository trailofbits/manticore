from seth import SEthereum
################ Script #######################

seth = SEthereum()
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
user_account = seth.create_account( balance=1000)


print "[+] Creating a contract account"
bytecode = seth.compile(source_code) 
#Initialize contract
# Note that the initialization argument would have been passed immediatelly 
# after the init bytecode  init=bytecode+pack(parameter)
contract_account = seth.create_contract(owner=user_account,
                                        init=bytecode)

   
print "[+] Now the symbolic values"

symbolic_data = seth.SByte(164) #seth.new_symbolic_buffer(label='msg.data.tx1', nbytes=164)
symbolic_value = None #seth.new_symbolic_value(256)

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



