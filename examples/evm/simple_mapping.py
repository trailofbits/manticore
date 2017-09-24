from seth import *
################ Script #######################

seth = SEthereum()
seth.verbosity(0)
#And now make the contract account to analyze
# cat  | solc --bin 
source_code = '''
pragma solidity ^0.4.13;

contract Test {
    event Log(string);
    mapping(address => uint) private balances;

    function Test(){
        balances[0x11111111111111111111111111111111] = 10;
        balances[0x22222222222222222222222222222222] = 20;
        balances[0x33333333333333333333333333333333] = 30;
        balances[0x44444444444444444444444444444444] = 40;
        balances[0x55555555555555555555555555555555] = 50;
    }
    
    function target(address key) returns (bool){
        if (balances[key] > 20)
            Log("Balance greater than 20");
        else
            Log("Balance less or equal than 20");
    } 

}
'''
user_account = seth.create_account(balance=1000)

#Initialize contract
bytecode = seth.compile(source_code)
contract_account = seth.create_contract(owner=user_account, 
                                          balance=0, 
                                          init_bytecode=bytecode)

symbolic_data = seth.new_symbolic_buffer(name='tx1.msg.data.', nbytes=64)
symbolic_value = seth.new_symbolic_value(256, label='tx1.value')
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


