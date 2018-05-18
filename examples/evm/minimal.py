from manticore.ethereum import ManticoreEVM, evm
################ Script #######################

m = ManticoreEVM()
m.verbosity(9)
#And now make the contract account to analyze
source_code = '''
contract InternalAttacker {
    function internalAttack(address _target) payable {
        address(this).call(bytes4(keccak256("dive(address)")), _target);
        msg.sender.transfer(this.balance);
    }
    function dive(address _target) {
        _target.transfer(this.balance);
        revert();
    }
}
'''

owner_account = m.create_account(balance=1000)
user_account = m.create_account(balance=1000)
target_account = m.create_account(balance=1000)
#contract_account = m.solidity_create_contract(source_code, owner=user_account)
init_bytecode = ManticoreEVM.compile(source_code, runtime=False, contract_name='InternalAttacker')
contract_account = m.create_contract(init_bytecode, owner=user_account)

print "[+] User account", user_account
print "[+] target account", target_account
print "[+] Contract account", contract_account
print "[+] Source code:"
print source_code

symbolic_data = m.SByte(16) 
symbolic_value = m.SValue()

m.transaction(caller=user_account,
                address=contract_account,
                data=symbolic_data,
                value=symbolic_value )


print target_account, m.get_balance(target_account)
print user_account, m.get_balance(user_account)
#Let seth know we are not sending more transactions 
m.finalize()
print "[+] Look for results in %s"% m.workspace
