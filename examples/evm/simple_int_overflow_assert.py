from manticore import *
from manticore.core.smtlib import ConstraintSet
from manticore.platforms import evm
from manticore.core.state import State


set_verbosity('EEEEMMMMCCCC')



#Make the constraint store
constraints = ConstraintSet()
#make the ethereum world state
world = evm.EVMWorld(constraints)

#make a bunch of user accounts
user_account = world.create_account(address=None, balance=1000)
attacker_account = world.create_account(address=None, balance=0)


#And now make the contract account to analyze
'''
pragma solidity ^0.4.13;

contract Test {
    uint private sellerBalance=0;
    
    function Test(uint initialBalance){
        sellerBalance += initialBalance;
    }
    
    function target(uint value) returns (bool){

        sellerBalance += value; // possible overflow
        assert(sellerBalance >= value); // auditor assert

    } 

}
'''

bytecote = '606060405260008055341561001357600080fd5b604051602080610115833981016040528080519060200190919050505b8060008082825401925050819055505b505b60c5806100506000396000f30060606040526000357c0100000000000000000000000000000000000000000000000000000000900463ffffffff1680639811c7c114603d575b600080fd5b3415604757600080fd5b605b60048080359060200190919050506075565b604051808215151515815260200191505060405180910390f35b60008160008082825401925050819055508160005410151515609357fe5b5b9190505600a165627a7a7230582061a5978237a74c48ff9f0aeadd9d2bae62116a5a44fc2130964499c20f2129f40029'.decode('hex')

#initialize contract with "50"
contract_account = world.create_contract(origin=user_account, 
                                              price=0, 
                                              address=None, 
                                              balance=0, 
                                              init=bytecote + evm.pack(0),
                                              run=True)

#This is how the world looks like now...
print world




def terminate_transaction_callback(m, state, *args):
    world = state.platform
    constraints = state.constraints
    step = initial_state.context['step']

    if step == 0:
        #Start the attack, this is a symbolic transaction. It should generate several world states.
        symbolic_data = constraints.new_array(256, name='TRANS1', index_max=256)
        world.transaction(address=contract_account,
                            origin=user_account,
                            price=0,
                            data=symbolic_data,
                            caller=user_account,
                            value=0,
                            header={'timestamp':1})
        state.input_symbols.append(symbolic_data)
        m.add(state)
    elif step == 1:
        #Start the attack, this is a symbolic transaction. It should generate several world states.
        symbolic_data = constraints.new_array(256, name='TRANS2', index_max=256)
        world.transaction(address=contract_account,
                            origin=user_account,
                            price=0,
                            data=symbolic_data,
                            caller=user_account,
                            value=0,
                            header={'timestamp':1})
        state.input_symbols.append(symbolic_data)
        state.input_symbols.append(symbolic_data)
        m.add(state)

    state.context['step'] = step+1


#Let's start with the symbols
initial_state = State(constraints, world)
initial_state.context['step'] = 0

m = Manticore()
m.add(initial_state)

#now when this transaction ends
m.subscribe('will_terminate_state', terminate_transaction_callback)

m.run()

#explore resulted states for one with funds in the attacker_account or whatever
# in ./workspace



