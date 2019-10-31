from manticore import ManticoreEVM

################ Script #######################

m = ManticoreEVM()

# And now make the contract account to analyze
# cat  | solc --bin
source_code = """
contract NoDistpatcher {
    event Log(string);

    function  named_func(uint x) public returns (uint) {
    return 5 + x;
    }

    function() external payable {
        if (msg.data[0] == 'A') {
            emit Log("Got an A");
        }
        else{
            emit Log("Got something else");
        }
    } 
}
"""

user_account = m.create_account(balance=1000, name="user_account")
print("[+] Creating a user account", user_account.name_)

contract_account = m.solidity_create_contract(
    source_code, owner=user_account, name="contract_account"
)
print("[+] Creating a contract account", contract_account.name_)
contract_account.named_func(1)

print("[+] Now the symbolic values")
symbolic_data = m.make_symbolic_buffer(320)
symbolic_value = m.make_symbolic_value(name="VALUE")
symbolic_address = m.make_symbolic_value(name="ADDRESS")
symbolic_caller = m.make_symbolic_value(name="CALLER")
m.transaction(
    caller=symbolic_caller, address=symbolic_address, data=symbolic_data, value=symbolic_value
)

# Let seth know we are not sending more transactions
m.finalize()
print(f"[+] Look for results in {m.workspace}")
