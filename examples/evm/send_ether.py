from manticore import *
from manticore.core.smtlib import ConstraintSet, Operators, solver
from manticore.platforms import evm
from manticore.core.state import State

set_verbosity('MMMMEEEEE')

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
        self.user_accounts = []

    def create_account(self, user=False, **kwargs):
        ''' Can only be used at the begining '''
        address = self.temp_initial_state.platform.create_account( **kwargs)
        if user:
            self.user_accounts.append(address)
        return address

    def create_contract(self, *args, **kwargs):
        ''' Can only be used at the begining '''
        return self.temp_initial_state.platform.create_contract(*args, **kwargs)

    def all_user_accounts(self, state):
        all_users_select = state.constraints.new_bitvec(16, '_aux_all_users')
        all_users = self.user_accounts[0]
        for i in range(len(self.user_accounts)-1):
            all_users = Operators.ITEBV(160, all_users_select==i+1, self.user_accounts[i+1], all_users)
        state.constraints.add(all_users_select < len(self.user_accounts))
        state.constraints.add(all_users_select >= 0)
        return all_users

    #Callbacks
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
    def will_execute_instruction_callback(self, state, instruction):
        print state.platform.current
        with self.locked_context('coverage', set) as coverage:
            coverage.add(state.platform.current.pc)

    def did_read_code(self, offset, size):
        with self.locked_context('code_data', set) as code_data:
            for i in range(offset, offset+size):
                code_data.add(i)

    def run(self, **kwargs):
        self.add(self.temp_initial_state)
        self.temp_initial_state = None
        #now when this transaction ends
        self._executor.subscribe('will_terminate_state', self.terminate_transaction_callback)
        self._executor.subscribe('will_execute_instruction', self.will_execute_instruction_callback)
        self._executor.subscribe('did_read_code', self.did_read_code)

        super(ManticoreEVM, self).run(**kwargs)

    def report(self, state, world, e):
        print "="*20
        print "REPORT:", e
        print world
        #print world
        '''
        for address, memlog, topics in state.platform.logs:
            try:
                print "LLLOG:", hex(address), ''.join(map(chr, memlog[12:])), topics
            except:
                print "LLLOG:", address,  memlog, topics

        #print state.constraints
        for expr in state.input_symbols:
            res = state.solve_one(expr)
            try:
                print expr.name,  res.encode('hex')
            except:
                print expr.name,  res
        '''

seth = ManticoreEVM()

#make a bunch of user accounts
owner_account = seth.create_account(address=None, balance=1000)
user1_account = seth.create_account(address=None, balance=2000, user=True)
#user2_account = seth.create_account(address=None, balance=1000, user=True)


#And now make the contract account to analyze
# cat coverage.sol | solc --bin 
#simple_mapping_read
bytecode = '60606040523415600e57600080fd5b5b5b5b603580601e6000396000f30060606040525b5b5b0000a165627a7a723058209d2bb527565127a616c5524558462e765780d5ac245751525b595ed766c041d30029'.decode('hex')

#Initialize contract
# We can do this without a @seth.transaction as all the arguments(none) are concrete
# Note that the initialization argument would have been passed immediatelly after
# the init bytecode
contract_account = seth.create_contract(origin=owner_account, 
                                              price=0, 
                                              address=None, 
                                              balance=0, 
                                              init=bytecode,
                                              run=True)

runtime_bytecode = seth.temp_initial_state.platform.storage[contract_account]['code']

#Potentially symbolic transactions. We can add an arbitrary number of transactions
# that wil run in sequence one after the other. To maintain a state this function
# can save private date into the state.context[].
@seth.transaction
def tx_1(m, state, world):
    #Start the analisys, this is a symbolic transaction. 
    #It may generate several world states.
    symbolic_data = state.new_symbolic_buffer(nbytes=256)
    user_account = m.all_user_accounts(state)
    world.transaction(address=contract_account,
                        origin=user_account,
                        price=0,
                        data=symbolic_data,
                        caller=user_account,
                        value=1234,
                        header={'timestamp':1})
    


#run run run   
seth.run()


seen = seth.context['coverage'].union( seth.context.get('code_data', set()))

print output
print "Total assembler lines:", count
print "Total assembler lines visited:", len(seen)
print "Coverage:", len(seen)*100.0/count , "%"



