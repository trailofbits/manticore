from manticore.ethereum import ManticoreEVM

m = ManticoreEVM()
m.verbosity(2)
# And now make the contract account to analyze
# cat  | solc --bin
source_code = """
pragma solidity ^0.4.13;

contract Test {
    event Log(string);
    mapping(address => uint) private balances;

    function Test(){
        balances[0x1111111111111111111111111111111111111111] = 10;
        balances[0x2222222222222222222222222222222222222222] = 20;
        balances[0x3333333333333333333333333333333333333333] = 30;
        balances[0x4444444444444444444444444444444444444444] = 40;
        balances[0x5555555555555555555555555555555555555555] = 50;
    }
    
    function target(address key) returns (bool){
        if (balances[key] > 20)
            Log("Balance greater than 20");
        else
            Log("Balance less or equal than 20");
    } 

}
"""
# Initialize accounts
user_account = m.create_account(balance=1000)
contract_account = m.solidity_create_contract(source_code, owner=user_account)

symbolic_data = m.make_symbolic_buffer(64)
symbolic_value = 0
m.transaction(
    caller=user_account, address=contract_account, value=symbolic_value, data=symbolic_data
)

m.finalize()
print(f"[+] Look for results in {m.workspace}")
