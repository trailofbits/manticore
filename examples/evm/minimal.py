from seth1 import SEthereum
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

'''print bytecode.encode('hex')
assert bytecode == '6060604052341561000f57600080fd5b5b6101d08061001f6000396000f30060606040525b5b7f41000000000000000000000000000000000000000000000000000000000000006000366000818110151561003757fe5b90509001357f010000000000000000000000000000000000000000000000000000000000000090047f0100000000000000000000000000000000000000000000000000000000000000027effffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff19167effffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff19161415610138577fcf34ef537ac33ee1ac626ca1587a0a7e8e51561e5514f8cb36afa1c5102b3bab6040518080602001828103825260088152602001807f476f7420616e204100000000000000000000000000000000000000000000000081525060200191505060405180910390a16101a1565b7fcf34ef537ac33ee1ac626ca1587a0a7e8e51561e5514f8cb36afa1c5102b3bab6040518080602001828103825260128152602001807f476f7420736f6d657468696e6720656c7365000000000000000000000000000081525060200191505060405180910390a15b5b0000a165627a7a72305820b3ecb10b6df219d9f054495bc3856a1f08263c74708f45919330121d027b808c0029'.decode('hex')
'''

#Initialize contract
# Note that the initialization argument would have been passed immediatelly 
# after the init bytecode  init=bytecode+pack(parameter)
contract_account = seth.create_contract(owner=user_account,
                                        init=bytecode)

   
print "[+] Now the symbolic values"

symbolic_data = seth.new_symbolic_buffer(label='msg.data.tx1', nbytes=164)
symbolic_value = seth.new_symbolic_value(256)

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



