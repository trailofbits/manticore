from manticore import *
from manticore.core.smtlib import ConstraintSet
from manticore.platforms import evm
from manticore.core.state import State

set_verbosity('')

class ManticoreEVM(Manticore):
    def transaction(self, transaction):
        self.transactions.append(transaction)
        return transaction

    def __init__(self):
        super(ManticoreEVM, self).__init__()
        #Make the constraint store
        constraints = ConstraintSet()
        #make the ethereum world state
        world = evm.EVMWorld(constraints)

        #Let's start with the symbols
        self.temp_initial_state = State(constraints, world)
        self.transactions = []

    def create_account(self, *args, **kwargs):
        ''' Can only be used at the begining '''
        return self.temp_initial_state.platform.create_account(*args, **kwargs)

    def create_contract(self, *args, **kwargs):
        ''' Can only be used at the begining '''
        return self.temp_initial_state.platform.create_contract(*args, **kwargs)


    def terminate_transaction_callback(self, state, state_id, e):
        ''' INTERNAL USE '''
        step = state.context.get('step',0)
        state.context['step'] = step + 1
        if step < len(self.transactions):
            self.transactions[step](self, state, state.platform)
            self.add(state)
            e.testcase = False
        else:
            self.report(state, state.platform, e)

    def run(self, **kwargs):
        self.add(self.temp_initial_state)
        self.temp_initial_state = None
        #now when this transaction ends
        self._executor.subscribe('will_terminate_state', self.terminate_transaction_callback)
        super(ManticoreEVM, self).run(**kwargs)

    def report(self, state, world, e):
        print "="*20
        print "REPORT:", e
        print world
        for address, memlog, topics in state.platform.logs:
            print "LLLOG:", hex(address), ''.join(map(chr, memlog[12:])), topics
        #print state.constraints
        for expr in state.input_symbols:
            print expr.name,  state.solve_one(expr).encode('hex')


seth = ManticoreEVM()

#make a bunch of user accounts
user_account = seth.create_account(address=None, balance=1000)
attacker_account = seth.create_account(address=None, balance=0)


#And now make the contract account to analyze
source_code = '''
/*
  Simple contract with a single public function
  It should produce only 2 forks
  */
  
pragma solidity ^0.4.13;

contract Test {
    event Log(string);

    function target(uint value) {

        if (value > 0x1000)
            Log("Greater than 0x1000");
        else
            Log("Lower or equal than 0x1000");
    } 
}

'''
# cat source_code | solc --bin 
bytecote = '6060604052341561000f57600080fd5b5b6101718061001f6000396000f30060606040526000357c0100000000000000000000000000000000000000000000000000000000900463ffffffff1680639811c7c11461003e575b600080fd5b341561004957600080fd5b61005f6004808035906020019091905050610061565b005b6110008111156100d8577fcf34ef537ac33ee1ac626ca1587a0a7e8e51561e5514f8cb36afa1c5102b3bab6040518080602001828103825260138152602001807f47726561746572207468616e203078313030300000000000000000000000000081525060200191505060405180910390a1610141565b7fcf34ef537ac33ee1ac626ca1587a0a7e8e51561e5514f8cb36afa1c5102b3bab60405180806020018281038252601a8152602001807f4c6f776572206f7220657175616c207468616e2030783130303000000000000081525060200191505060405180910390a15b5b505600a165627a7a72305820e8b36de8e84d8fca292b2b814dbb072263fe971830e592ebf9d77dfd40136a7b0029'.decode('hex')

#Initialize contract
# We can do this without a @seth.transaction as all the arguments(none) are concrete
# Note that the initialization argument would have been passed immediatelly after
# the init bytecode
contract_account = seth.create_contract(origin=user_account, 
                                              price=0, 
                                              address=None, 
                                              balance=0, 
                                              init=bytecote,
                                              run=True)


#Potentially symbolic transactions. We can add an arbitrary number of transactions
# that wil run in sequence one after the other. To maintain a state this function
# can save private date into the state.context[].
@seth.transaction
def tx_1(m, state, world):
    #Start the analisys, this is a symbolic transaction. 
    #It may generate several world states.
    symbolic_data = state.new_symbolic_buffer(nbytes=256)
    world.transaction(address=contract_account,
                        origin=user_account,
                        price=0,
                        data=symbolic_data,
                        caller=user_account,
                        value=0,
                        header={'timestamp':1})
#run run run   
seth.run()


