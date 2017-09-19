from seth import *
################ Script #######################

seth = SEthereum()
seth.verbosity(0)
#And now make the contract account to analyze
# cat  | solc --bin 
'''
pragma solidity ^0.4.13;

contract Test {
    event Log(string);
    mapping(address => uint) private balances;

    function Test(){
        balances[100] = 10;
        balances[200] = 20;
        balances[300] = 30;
        balances[400] = 40;
        balances[500] = 50;
    }
    
    function target(address key) returns (bool){
        if (balances[key] > 20)
            Log("Balance greater than 20");
        else
            Log("Balance less or equal than 20");
    } 

}
'''

@seth.init
def init(state):
    global user_account, contract_account, runtime_bytecode
    world = state.platform

    user_account = world.create_account(address=None, balance=1000)

    bytecode = '6060604052341561000f57600080fd5b5b600a600080606473ffffffffffffffffffffffffffffffffffffffff16815260200190815260200160002081905550601460008060c873ffffffffffffffffffffffffffffffffffffffff16815260200190815260200160002081905550601e60008061012c73ffffffffffffffffffffffffffffffffffffffff16815260200190815260200160002081905550602860008061019073ffffffffffffffffffffffffffffffffffffffff1681526020019081526020016000208190555060326000806101f473ffffffffffffffffffffffffffffffffffffffff168152602001908152602001600020819055505b5b6101e08061010f6000396000f30060606040526000357c0100000000000000000000000000000000000000000000000000000000900463ffffffff168063dad9da8a1461003e575b600080fd5b341561004957600080fd5b610075600480803573ffffffffffffffffffffffffffffffffffffffff1690602001909190505061008f565b604051808215151515815260200191505060405180910390f35b600060146000808473ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff168152602001908152602001600020541115610145577fcf34ef537ac33ee1ac626ca1587a0a7e8e51561e5514f8cb36afa1c5102b3bab6040518080602001828103825260178152602001807f42616c616e63652067726561746572207468616e20323000000000000000000081525060200191505060405180910390a16101ae565b7fcf34ef537ac33ee1ac626ca1587a0a7e8e51561e5514f8cb36afa1c5102b3bab60405180806020018281038252601d8152602001807f42616c616e6365206c657373206f7220657175616c207468616e20323000000081525060200191505060405180910390a15b5b9190505600a165627a7a723058201b2817561b5630cbc3fe5aaffc4eed5eba5309cb1c2b8595a586f97064e0a63b0029'.decode('hex')

    #Initialize contract
    # Note that the initialization argument would have been passed immediatelly 
    # after the init bytecode  init=bytecode+pack(parameter)
    contract_account = world.create_contract(origin=user_account, 
                                                  price=0, 
                                                  address=None, 
                                                  balance=0, 
                                                  init=bytecode, 
                                                  run=True)



#Potentially symbolic transactions. We can add an arbitrary number of transactions
#that will run in sequence one after the other. To maintain a state this function
#can save private date into the state.context[].
@seth.transaction
def tx_1(m, state, world):
    global user_account, contract_account, runtime_bytecode

    #symbolic_data represents all possible data (of 16 bytes)
    #Using it as input will potentially fork the analysis and generate several 
    #world states
    symbolic_data = state.new_symbolic_buffer(name='msg.data', nbytes=64)
    world.transaction(address=contract_account,
                        origin=user_account,
                        price=0,
                        data=symbolic_data,
                        caller=user_account,
                        value=0,
                        header={'timestamp':1})

#run run run   
seth.run()

print seth.coverage(contract_account)



