from manticore.seth import ManticoreEVM
seth = ManticoreEVM()
#And now make the contract account to analyze
source_code = '''
pragma solidity ^0.4.15;
contract Overflow {
    uint private sellerBalance=0;
    
    function add(uint value) returns (bool){
        sellerBalance += value; // complicated math with possible overflow

        // possible auditor assert
        assert(sellerBalance >= value); 
    } 
}
'''
#Initialize user and contracts
user_account = seth.create_account(balance=1000)
contract_account = seth.solidity_create_contract(source_code, owner=user_account, balance=0)

#First add won't overflow uint256 representation
contract_account.add(seth.SValue)

#Potential overflow
contract_account.add(seth.SValue)


print "[+] There are %d reverted states now"% len(seth.final_state_ids)
for state_id in seth.final_state_ids:
    print seth.report(state_id)

print "[+] There are %d alive states now"% len(seth.running_state_ids)
for state_id in seth.running_state_ids:
    print seth.report(state_id)

print "[+] Global coverage: %x"% contract_account
print seth.coverage(contract_account)


