from manticore import *
from manticore.core.smtlib import ConstraintSet, Operators, solver
from manticore.platforms import evm
from manticore.core.state import State

#set_verbosity('MMMMEEEEECCCCSSSS')

class ManticoreEVM(Manticore):
    def transaction(self, transaction):
        self.transactions.append(transaction)
        return transaction

    def __init__(self):
        #Make the constraint store
        constraints = ConstraintSet()
        #make the ethereum world state
        world = evm.EVMWorld(constraints)

        #Let's start with the symbols
        self.temp_initial_state = State(constraints, world)
        super(ManticoreEVM, self).__init__(self.temp_initial_state)
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
            self.enqueue(state)
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
        self.enqueue(self.temp_initial_state)
        self.temp_initial_state = None
        #now when this transaction ends
        self._executor.subscribe('will_terminate_state', self.terminate_transaction_callback)
        self._executor.subscribe('will_execute_instruction', self.will_execute_instruction_callback)
        self._executor.subscribe('did_read_code', self.did_read_code)

        super(ManticoreEVM, self).run(**kwargs)

    def report(self, state, world, e):
        print "="*20
        print "REPORT:", e
        #print world
        for address, memlog, topics in state.platform.logs:
            print "LLLOG:", hex(address), ''.join(map(chr, memlog[12:])), topics
        #print state.constraints
        for expr in state.input_symbols:
            res = state.solve_one(expr)
            try:
                print expr.name,  res.encode('hex')
            except:
                print expr.name,  res


seth = ManticoreEVM()

#make a bunch of user accounts
owner_account = seth.create_account(address=None, balance=1000)
user1_account = seth.create_account(address=None, balance=1000, user=True)
user2_account = seth.create_account(address=None, balance=1000, user=True)


#And now make the contract account to analyze
# cat coverage.sol | solc --bin 
bytecode = '606060405260008060146101000a81548160ff021916908315150217905550341561002957600080fd5b5b336000806101000a81548173ffffffffffffffffffffffffffffffffffffffff021916908373ffffffffffffffffffffffffffffffffffffffff1602179055505b5b6109968061007b6000396000f30060606040526000357c0100000000000000000000000000000000000000000000000000000000900463ffffffff1680630cf044ee1461005f57806370a0823114610074578063d8e1b9ba146100c1578063ebb5f11c1461010e575b600080fd5b341561006a57600080fd5b61007261015b565b005b341561007f57600080fd5b6100ab600480803573ffffffffffffffffffffffffffffffffffffffff169060200190919050506101d5565b6040518082815260200191505060405180910390f35b34156100cc57600080fd5b61010c600480803590602001909190803573ffffffffffffffffffffffffffffffffffffffff16906020019091908035151590602001909190505061021f565b005b341561011957600080fd5b610159600480803590602001909190803573ffffffffffffffffffffffffffffffffffffffff169060200190919080351515906020019091905050610449565b005b6000809054906101000a900473ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff163373ffffffffffffffffffffffffffffffffffffffff161415156101b657600080fd5b6001600060146101000a81548160ff0219169083151502179055505b5b565b6000600160008373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff1681526020019081526020016000205490505b919050565b60008060149054906101000a900460ff16151561023b57600080fd5b81156102f95761024b3385610828565b61025583856108c8565b7f26162814817e23ec5035d6a2edc6c422da2da2119e27cfca6be65cc2dc55ca4c338486604051808473ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff1681526020018373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff168152602001828152602001935050505060405180910390a1610441565b600160003373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff16815260200190815260200160002054600160008573ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff16815260200190815260200160002054039050838111610389578061038b565b835b935061039733856108c8565b6103a18385610828565b7f9bbd814328e65758b36306475bbc61410445dd088c88681ed74c940dc604db1a338486604051808473ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff1681526020018373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff168152602001828152602001935050505060405180910390a15b5b5b50505050565b600080600160003373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff1681526020019081526020016000205414156104dc57602a600160003373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff16815260200190815260200160002081905550610822565b811561059a576104ec3385610828565b6104f683856108c8565b7f26162814817e23ec5035d6a2edc6c422da2da2119e27cfca6be65cc2dc55ca4c338486604051808473ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff1681526020018373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff168152602001828152602001935050505060405180910390a1610821565b600160003373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff16815260200190815260200160002054600160008573ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff16815260200190815260200160002054111561076c57600160003373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff16815260200190815260200160002054600160008573ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff168152602001908152602001600020540390508381116106b057806106b2565b835b93506106be33856108c8565b6106c88385610828565b7f9bbd814328e65758b36306475bbc61410445dd088c88681ed74c940dc604db1a338486604051808473ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff1681526020018373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff168152602001828152602001935050505060405180910390a1610820565b6107763385610828565b61078083856108c8565b7f26162814817e23ec5035d6a2edc6c422da2da2119e27cfca6be65cc2dc55ca4c338486604051808473ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff1681526020018373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff168152602001828152602001935050505060405180910390a15b5b5b50505050565b80600160008473ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff168152602001908152602001600020541015151561087657600080fd5b80600160008473ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff168152602001908152602001600020600082825403925050819055505b5050565b8081600160008573ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff16815260200190815260200160002054011015151561091857600080fd5b80600160008473ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff168152602001908152602001600020600082825401925050819055505b50505600a165627a7a7230582027deeaa4fba35d84ca3f5dacc38cf2920cc9abaa42312c7186189758a4c58e030029'.decode('hex')

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
    symbolic_value = state.new_symbolic_value(256, label='value')
    user_account = user1_account #m.all_user_accounts(state)
    world.transaction(address=contract_account,
                        origin=user_account,
                        price=0,
                        data=symbolic_data,
                        caller=user_account,
                        value=symbolic_value,
                        header={'timestamp':1})

#@seth.transaction
def tx_2(m, state, world):
    #Start the analisys, this is a symbolic transaction. 
    #It may generate several world states.
    symbolic_data = state.new_symbolic_buffer(nbytes=256)
    symvolic_value = state.new_symbolic_value(self, 256, label='value')
    user_account = user2_account #m.all_user_accounts(state)
    world.transaction(address=contract_account,
                        origin=user_account,
                        price=0,
                        data=symbolic_data,
                        caller=user_account,
                        value=symbolic_value,
                        header={'timestamp':1})
#run run run   
seth.run()


seen = seth.context['coverage'].union( seth.context.get('code_data', set()))


class bcolors:
    HEADER = '\033[95m'
    OKBLUE = '\033[94m'
    OKGREEN = '\033[92m'
    WARNING = '\033[93m'
    FAIL = '\033[91m'
    ENDC = '\033[0m'
    BOLD = '\033[1m'
    UNDERLINE = '\033[4m'

output = ''
address = 0
count = 0
for i in evm.EVMDecoder.decode_all(runtime_bytecode) :
    if address in seen:
        output += bcolors.OKGREEN
        output += "** 0x%04x %s\n"%(address, i)
        output += bcolors.ENDC
    else:
        output += "   0x%04x %s\n"%(address, i)
    address += i.size
    count += 1
print output
print "Total assembler lines:", count
print "Total assembler lines visited:", len(seen)
print "Coverage:", len(seen)*100.0/count , "%"



