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

@seth.init
def init(state):
    global user_account, contract_account, runtime_bytecode
    world = state.platform

    user_account = world.create_account(address=None, balance=1000)

    bytecode = '6060604052341561000f57600080fd5b5b600a6000806f1111111111111111111111111111111173ffffffffffffffffffffffffffffffffffffffff1681526020019081526020016000208190555060146000806f2222222222222222222222222222222273ffffffffffffffffffffffffffffffffffffffff16815260200190815260200160002081905550601e6000806f3333333333333333333333333333333373ffffffffffffffffffffffffffffffffffffffff1681526020019081526020016000208190555060286000806f4444444444444444444444444444444473ffffffffffffffffffffffffffffffffffffffff1681526020019081526020016000208190555060326000806f5555555555555555555555555555555573ffffffffffffffffffffffffffffffffffffffff168152602001908152602001600020819055505b5b6101e0806101576000396000f30060606040526000357c0100000000000000000000000000000000000000000000000000000000900463ffffffff168063dad9da8a1461003e575b600080fd5b341561004957600080fd5b610075600480803573ffffffffffffffffffffffffffffffffffffffff1690602001909190505061008f565b604051808215151515815260200191505060405180910390f35b600060146000808473ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff168152602001908152602001600020541115610145577fcf34ef537ac33ee1ac626ca1587a0a7e8e51561e5514f8cb36afa1c5102b3bab6040518080602001828103825260178152602001807f42616c616e63652067726561746572207468616e20323000000000000000000081525060200191505060405180910390a16101ae565b7fcf34ef537ac33ee1ac626ca1587a0a7e8e51561e5514f8cb36afa1c5102b3bab60405180806020018281038252601d8152602001807f42616c616e6365206c657373206f7220657175616c207468616e20323000000081525060200191505060405180910390a15b5b9190505600a165627a7a7230582039e602661de747577bd04bb5206dfe878e21ef215ecca262ede8913c3577a8c80029'.decode('hex')

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



