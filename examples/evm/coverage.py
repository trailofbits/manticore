from seth import *
################ Script #######################

seth = SEthereum()
seth.verbosity(0)
#And now make the contract account to analyze
# cat coverage.py | solc --bin 

@seth.init
def init(state):
    global user_account, contract_account, runtime_bytecode
    world = state.platform

    user_account = world.create_account(address=None, balance=1000)


    bytecode = '606060405260008060146101000a81548160ff021916908315150217905550341561002957600080fd5b5b336000806101000a81548173ffffffffffffffffffffffffffffffffffffffff021916908373ffffffffffffffffffffffffffffffffffffffff1602179055505b5b6109968061007b6000396000f30060606040526000357c0100000000000000000000000000000000000000000000000000000000900463ffffffff1680630cf044ee1461005f57806370a0823114610074578063d8e1b9ba146100c1578063ebb5f11c1461010e575b600080fd5b341561006a57600080fd5b61007261015b565b005b341561007f57600080fd5b6100ab600480803573ffffffffffffffffffffffffffffffffffffffff169060200190919050506101d5565b6040518082815260200191505060405180910390f35b34156100cc57600080fd5b61010c600480803590602001909190803573ffffffffffffffffffffffffffffffffffffffff16906020019091908035151590602001909190505061021f565b005b341561011957600080fd5b610159600480803590602001909190803573ffffffffffffffffffffffffffffffffffffffff169060200190919080351515906020019091905050610449565b005b6000809054906101000a900473ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff163373ffffffffffffffffffffffffffffffffffffffff161415156101b657600080fd5b6001600060146101000a81548160ff0219169083151502179055505b5b565b6000600160008373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff1681526020019081526020016000205490505b919050565b60008060149054906101000a900460ff16151561023b57600080fd5b81156102f95761024b3385610828565b61025583856108c8565b7f26162814817e23ec5035d6a2edc6c422da2da2119e27cfca6be65cc2dc55ca4c338486604051808473ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff1681526020018373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff168152602001828152602001935050505060405180910390a1610441565b600160003373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff16815260200190815260200160002054600160008573ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff16815260200190815260200160002054039050838111610389578061038b565b835b935061039733856108c8565b6103a18385610828565b7f9bbd814328e65758b36306475bbc61410445dd088c88681ed74c940dc604db1a338486604051808473ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff1681526020018373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff168152602001828152602001935050505060405180910390a15b5b5b50505050565b600080600160003373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff1681526020019081526020016000205414156104dc57602a600160003373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff16815260200190815260200160002081905550610822565b811561059a576104ec3385610828565b6104f683856108c8565b7f26162814817e23ec5035d6a2edc6c422da2da2119e27cfca6be65cc2dc55ca4c338486604051808473ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff1681526020018373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff168152602001828152602001935050505060405180910390a1610821565b600160003373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff16815260200190815260200160002054600160008573ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff16815260200190815260200160002054111561076c57600160003373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff16815260200190815260200160002054600160008573ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff168152602001908152602001600020540390508381116106b057806106b2565b835b93506106be33856108c8565b6106c88385610828565b7f9bbd814328e65758b36306475bbc61410445dd088c88681ed74c940dc604db1a338486604051808473ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff1681526020018373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff168152602001828152602001935050505060405180910390a1610820565b6107763385610828565b61078083856108c8565b7f26162814817e23ec5035d6a2edc6c422da2da2119e27cfca6be65cc2dc55ca4c338486604051808473ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff1681526020018373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff168152602001828152602001935050505060405180910390a15b5b5b50505050565b80600160008473ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff168152602001908152602001600020541015151561087657600080fd5b80600160008473ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff168152602001908152602001600020600082825403925050819055505b5050565b8081600160008573ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff16815260200190815260200160002054011015151561091857600080fd5b80600160008473ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff168152602001908152602001600020600082825401925050819055505b50505600a165627a7a72305820803c2088bd25cb61164a2a8ffe5dd99726bcebd9dd2c84cef1b6a8de418a802b0029'.decode('hex')
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
    symbolic_data = state.new_symbolic_buffer(name='msg.data.tx1', nbytes=164)
    symbolic_value = state.new_symbolic_value(name='value.tx1', 256)
    world.transaction(address=contract_account,
                        origin=user_account,
                        price=0,
                        data=symbolic_data,
                        caller=user_account,
                        value=symbolic_value,
                        header={'timestamp':1})


@seth.transaction
def tx_2(m, state, world):
    global user_account, contract_account, runtime_bytecode

    #symbolic_data represents all possible data (of 16 bytes)
    #Using it as input will potentially fork the analysis and generate several 
    #world states
    symbolic_data = state.new_symbolic_buffer(name='msg.data.tx2', nbytes=164)
    symbolic_value = state.new_symbolic_value(name='value.tx2', 256)
    world.transaction(address=contract_account,
                        origin=user_account,
                        price=0,
                        data=symbolic_data,
                        caller=user_account,
                        value=symbolic_value,
                        header={'timestamp':1})
#run run run   
seth.run(procs = 8)

print seth.coverage(contract_account)



