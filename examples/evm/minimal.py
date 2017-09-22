from seth import *
################ Script #######################

seth = SEthereum()
seth.verbosity(0)
#And now make the contract account to analyze
# cat  | solc --bin 
'''
pragma solidity ^0.4.13;
contract NoDistpatcher {
    event Log(string);
    function() payable {
        if (msg.data[0] == 'A') {
            Log("Got an A");
        }
        else{
            Log("Got something else");
        }
    } 
}
'''

@seth.init
def init(state):
    global user_account, contract_account
    world = state.platform

    user_account = world.create_account(address=None, balance=1000)

    bytecode = '6060604052341561000f57600080fd5b5b6101d08061001f6000396000f30060606040525b5b7f41000000000000000000000000000000000000000000000000000000000000006000366000818110151561003757fe5b90509001357f010000000000000000000000000000000000000000000000000000000000000090047f0100000000000000000000000000000000000000000000000000000000000000027effffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff19167effffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff19161415610138577fcf34ef537ac33ee1ac626ca1587a0a7e8e51561e5514f8cb36afa1c5102b3bab6040518080602001828103825260088152602001807f476f7420616e204100000000000000000000000000000000000000000000000081525060200191505060405180910390a16101a1565b7fcf34ef537ac33ee1ac626ca1587a0a7e8e51561e5514f8cb36afa1c5102b3bab6040518080602001828103825260128152602001807f476f7420736f6d657468696e6720656c7365000000000000000000000000000081525060200191505060405180910390a15b5b0000a165627a7a72305820b3ecb10b6df219d9f054495bc3856a1f08263c74708f45919330121d027b808c0029'.decode('hex')

    #Initialize contract
    # Note that the initialization argument would have been passed immediatelly 
    # after the init bytecode  init=bytecode+pack(parameter)
    contract_account = world.create_contract(origin=user_account, 
                                              address=None, 
                                              balance=0, 
                                              init=bytecode, 
                                              run=True)

    


#Potentially symbolic transactions. We can add an arbitrary number of transactions
#that will run in sequence one after the other. To maintain a state this function
#can save private date into the state.context[].
@seth.transaction
def tx_1(m, state, world):
    global user_account, contract_account

    #symbolic_data represents all possible data (of 16 bytes)
    #Using it as input will potentially fork the analysis and generate several 
    #world states
    symbolic_data = state.new_symbolic_buffer(name='msg.data.tx1', nbytes=164)
    symbolic_value = state.new_symbolic_value(256)

    world.transaction(  caller=user_account,
                        address=contract_account,
                        data=symbolic_data,
                        value=symbolic_value )



#run run run   
seth.run()

print seth.coverage(contract_account)



