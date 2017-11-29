from manticore.seth import ManticoreEVM
################ Script #######################

seth = ManticoreEVM()
seth.verbosity(0)
#And now make the contract account to analyze
# cat  | solc --bin 
source_code = '''
pragma solidity ^0.4.13;

contract Test {
    event Log(string);
    mapping(address => uint) private balances;

    function Test() {}
    function target1() public {} 
    function target2() internal {} 
    function target3() private {} 
    function() {}

}
'''
#Initialize accounts
user_account = seth.create_account(balance=1000)
contract_account = seth.solidity_create_contract(source_code, owner=user_account)

symbolic_data = seth.SByte(4) 
symbolic_value = None 
seth.transaction(  caller=user_account,
                   address=contract_account,
                   value=symbolic_value,
                   data=symbolic_data
                 )


print "[+] There are %d reverted states now"% len(seth.final_state_ids)
for state_id in seth.final_state_ids:
    seth.report(state_id)

print "[+] There are %d alive states now"% len(seth.running_state_ids)
for state_id in seth.running_state_ids:
    seth.report(state_id)

print "[+] Global coverage:"
print seth.coverage(contract_account)


