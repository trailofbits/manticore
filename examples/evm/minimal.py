from manticore.ethereum import ManticoreEVM, evm
################ Script #######################

m = ManticoreEVM()
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

user_account = m.create_account(balance=1000)
print "[+] Creating a user account", user_account

init_bytecode = m.compile(source_code)
print "[+] Source code:"
print source_code

print "[+] Init bytecode:", init_bytecode.encode('hex')
print "[+] EVM init assembler:"
for instr in evm.EVMAsm.disassemble_all(init_bytecode[:-44]):
    print hex(instr.offset), instr



contract_account = m.create_contract(owner=user_account,
                                        init=init_bytecode)
print "[+] Creating a contract account", contract_account


print "[+] Now the symbolic values"
symbolic_data = m.make_symbolic_buffer(320) 
symbolic_value = None 
m.transaction(caller=user_account,
                address=contract_account,
                data=symbolic_data,
                value=symbolic_value )

#Let seth know we are not sending more transactions 
m.finalize()
print "[+] Look for results in %s"% m.workspace
