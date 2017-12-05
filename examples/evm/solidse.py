from manticore.seth import ManticoreEVM
import sys
################ Script #######################

seth = ManticoreEVM()
seth.verbosity(0)
#And now make the contract account to analyze
# cat  | solc --bin 
source_code = file(sys.argv[1],'rb').read()

user_account = seth.create_account(balance=1000)
print "[+] Creating a user account", user_account


contract_account = seth.solidity_create_contract(source_code, owner=user_account)
print "[+] Creating a contract account", contract_account

attacker_account = seth.create_account(balance=1000)
print "[+] Creating a attacker account", attacker_account



last_coverage = 0 
tx_count = 0
while True:

    symbolic_data = seth.SByte(320) 
    symbolic_value = None 
    seth.transaction(caller=attacker_account,
                    address=contract_account,
                    data=symbolic_data,
                    value=symbolic_value )
    new_coverage = seth.global_coverage(contract_account)
    tx_count += 1
    print "[+] Coverage after %d transactions: %d%%"%(tx_count, new_coverage)
    print "[+] There are %d reverted states now"% len(seth.final_state_ids)
    print "[+] There are %d alive states now"% len(seth.running_state_ids)
    if new_coverage == last_coverage:
        break
    last_coverage = new_coverage

print "[+] Coverage after %d transactions: %d%%"%(2, seth.global_coverage(contract_account))
#print "[+] There are %d reverted states now"% len(seth.final_state_ids)
#for state_id in seth.final_state_ids:
#    print seth.report(state_id)

print "[+] There are %d alive states now"% len(seth.running_state_ids)
for state_id in seth.running_state_ids:
    output = seth.report(state_id, ty = 'SELFDESTRUCT')
    if output is not None:
        print output 

print "[+] Global coverage:"
print seth.coverage(contract_account)



