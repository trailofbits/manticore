from seth import *

seth = ManticoreEVM()
seth.verbosity(3)
#And now make the contract account to analyze
source_code = file('coverage.sol').read()

user_account = seth.create_account(balance=1000)

bytecode = seth.compile(source_code)
#Initialize contract
contract_account = seth.create_contract(owner=user_account, 
                                          balance=0, 
                                          init=bytecode)

seth.transaction(  caller=user_account,
                    address=contract_account,
                    value=None,
                    data=seth.SByte(164),
                 )

#Up to here we get only ~30% coverage. 
#We need 2 transactions to fully explore the contract
seth.transaction(  caller=user_account,
                    address=contract_account,
                    value=None,
                    data=seth.SByte(164),
                 )

print "[+] There are %d reverted states now"% len(seth.final_state_ids)
print "[+] There are %d alive states now"% len(seth.running_state_ids)
for state_id in seth.running_state_ids:
    seth.report(state_id)

print "[+] Global coverage: %x"% contract_account
print seth.coverage(contract_account)


