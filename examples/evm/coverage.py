from seth import *
################ Script #######################

seth = SEthereum()
seth.verbosity(0)
#And now make the contract account to analyze
source_code = file('coverage.sol').read()

user_account = seth.create_account(balance=1000)

bytecode = seth.compile(source_code)
#Initialize contract
contract_account = seth.create_contract(owner=user_account, 
                                          balance=0, 
                                          init_bytecode=bytecode)

symbolic_data = seth.new_symbolic_buffer(name='tx1.msg.data.', nbytes=164)
symbolic_value = seth.new_symbolic_value(256, label='tx1.value')
seth.transaction(  caller=user_account,
                    address=contract_account,
                    value=symbolic_value,
                    data=symbolic_data,
                 )

#Up to here we get onle ~30% coverage. 
#We need 2 transactions to fully explore the contract

symbolic_data = seth.new_symbolic_buffer(name='tx2.msg.data.', nbytes=164)
symbolic_value = seth.new_symbolic_value(256, label='tx2.value')
seth.transaction(  caller=user_account,
                    address=contract_account,
                    value=symbolic_value,
                    data=symbolic_data,
                 )

print "[+] There are %d reverted states now"% len(seth.final_state_ids)
for state_id in seth.final_state_ids:
    seth.report(state_id)

print "[+] There are %d alive states now"% len(seth.running_state_ids)
for state_id in seth.running_state_ids:
    seth.report(state_id)

print "[+] Global coverage:"
print seth.coverage(contract_account)


