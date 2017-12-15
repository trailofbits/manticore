from manticore.seth import ManticoreEVM
################ Script #######################

m = ManticoreEVM()
m.verbosity(2)
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
user_account = m.create_account(balance=1000)
contract_account = m.solidity_create_contract(source_code, owner=user_account)

symbolic_data = m.make_symbolic_buffer(4) 
symbolic_value = None 
m.transaction(  caller=user_account,
                   address=contract_account,
                   value=symbolic_value,
                   data=symbolic_data
                 )

m.finalize()
print "[+] Look for results in %s"% m.workspace

