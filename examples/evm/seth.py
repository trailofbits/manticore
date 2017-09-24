from manticore import Manticore
from manticore.core.smtlib import ConstraintSet, Operators, solver, issymbolic, Array
from manticore.platforms import evm
from manticore.platforms.evm import pack_msb
from manticore.core.state import State
import tempfile
from subprocess import Popen, PIPE

solc = "/usr/bin/solc"

def parse_bin(buf):
    """
    Parse the output of solc
    Return a dict [name: bytecode]
    """
    ret = {}
    i = 0
    while i < len(buf):
        # looks for bytecode
        if buf[i].startswith('==='):
            # parse the name of the contract
            name = buf[i][buf[i].find(':')+1:buf[i].rfind(' =')]
            # parse the bytecode
            bytecode = buf[i+2]
            if len(bytecode) > 4: #avoid empty bytecode
                bytecode = bytecode.replace('\n', '') # remove '\n'                
                bytecode = bytecode.decode('hex') # convert to hex
                ret[name] = bytecode
            i = i+3
        else:
            i = i+1
    assert len(ret.values())==1
    return ret.values()[0]

def compile_code(source_code):
    """
    Compile a solidity source code
    Return a list [(contract_name, bytecode)]
    """
    with tempfile.NamedTemporaryFile() as temp:
        temp.write(source_code)
        temp.flush()
        p = Popen([solc, '--bin', temp.name], stdout=PIPE)
        outp = p.stdout.readlines()
        return parse_bin(outp)

class SEthereum(Manticore):
    @staticmethod
    def compile(source_code):
        return compile_code(source_code)

    def __init__(self):
        self.code = {}
        self._pending_transaction = None
        self._saved_states = []
        self._final_states = []
        #Make the constraint store
        constraints = ConstraintSet()
        #make the ethereum world state
        world = evm.EVMWorld(constraints)
        initial_state = State(constraints, world)
        super(SEthereum, self).__init__(initial_state)


        self._executor.subscribe('did_load_state', self.load_state_callback)
        self._executor.subscribe('will_terminate_state', self.terminate_state_callback)
        self._executor.subscribe('will_execute_instruction', self.will_execute_instruction_callback)
        self._executor.subscribe('did_read_code', self.did_read_code)
        self._executor.subscribe('symbolic_sha3', self.symbolic_sha3)
        self._executor.subscribe('concrete_sha3', self.concrete_sha3)

    @property
    def world(self):
        assert len(self._saved_states) == 0
        return self.initial_state.platform

    @property
    def running_state_ids(self):
        if self.initial_state is not None:
            return self._saved_states + [-1]
        else:
            return self._saved_states

    @property
    def final_state_ids(self):
        return self._final_states

    def get_world(self, state_id):
        if state_id == -1:
            return self.initial_state.platform

        state = self._executor._workspace.load_state(state_id, delete=False)
        return state.platform

    def create_contract(self, owner, balance=0, init=None, address=None):
        ''' Only available when there is a single state of the world'''
        assert self._pending_transaction is None
        assert init is not None
        address = self.world._new_address()
        self._pending_transaction = ('CREATE_CONTRACT', owner, address, balance, init)

        self.run()

        return address

    def create_account(self, balance=0, address=None):
        ''' Only available when there is a single state of the world'''
        assert self._pending_transaction is None
        return self.world.create_account( address, balance, code='', storage=None)
    '''
    @staticmethod
    def _check_bitsize(value, size):
        return isinstance(value, Bitvec) and function_id.size == size or (function_id & ~((1<<size)-1)) == 0
function_id, *args):
        assert self._pending_transaction is None
        assert self._check_bitsize(function_id, 32)
        assert all(self._check_vitsize(arg, 256) for arg in args)
    '''
    def transaction(self, caller, address, value, data):
        self._pending_transaction = ('CALL', caller, address, value, data)
        self.run()

    def run(self, **kwargs):
        #Ther is a pending transaction
        assert self._pending_transaction is not None
        #there is no states added to the executor queue
        assert len(self._executor.list()) == 0
        #there is at least one states in seth saved states
        assert len(self._saved_states) + int(self.initial_state is not None) > 0

        for state_id in self._saved_states:
            self._executor.put(state_id)
        self._saved_states = []

        result = super(SEthereum, self).run(**kwargs)

        if len(self._saved_states)==1:
            self._initial_state = self._executor._workspace.load_state(self._saved_states[0], delete=True)
            self._saved_states = []

        #clear pending transcations. We are done.
        self._pending_transaction = None
          
    def save(self, state, final=False):
        #save the state to secondary storage
        state_id = self._executor._workspace.save_state(state)

        if final:
            #Keep it on a private list
            self._final_states.append(state_id)
        else:
            #Keep it on a private list
            self._saved_states.append(state_id)
        return state_id

    #Callbacks
    def terminate_state_callback(self, state, state_id, e):
        ''' INTERNAL USE 
            Every time a state finishes executing last transaction we save it in
            our private list 
        '''
        state.context['last_exception'] = e

        if e.message != 'REVERT':
            # if not a revert we save the state for further transactioning
            state.context['processed'] = False
            if e.message == 'RETURN':
                ty, caller, address, value, data = self._pending_transaction
                if ty == 'CREATE_CONTRACT':
                    world = state.platform
                    world.storage[address]['code'] = world.last_return
            self.save(state)
            e.testcase = False  #Do not generate a testcase file
        else:
            self.save(state, final=True)



    #Callbacks
    def load_state_callback(self, state, state_id):
        ''' INTERNAL USE 
            When a state was just loaded from stoage we do the pending transaction
        '''

        if state.context.get('processed', False):
            return
        world = state.platform
        state.context['processed'] = True
        ty, caller, address, value, data = self._pending_transaction

        if isinstance (value, tuple):
            func, args, kwargs = value
            value = getattr(state, func)(*args, **kwargs)
        if isinstance (data, tuple):
            func, args, kwargs = data
            data = getattr(state, func)(*args, **kwargs)


        if ty == 'CALL':
            world.transaction(address=address, caller=caller, data=data, value=value)
        else:
            assert ty == 'CREATE_CONTRACT'
            world.create_contract(caller=caller, address=address, balance=value, init=data)


    def new_symbolic_buffer(self, *args, **kwargs):
        return 'new_symbolic_buffer', args, kwargs
    def new_symbolic_value(self, *args, **kwargs):
        return 'new_symbolic_value', args, kwargs
    
    def will_execute_instruction_callback(self, state, instruction):
        assert state.constraints == state.platform.constraints
        assert state.platform.constraints == state.platform.current.constraints

        #print state.platform.current
        #print solver.check(state.constraints)
        with self.locked_context('coverage', set) as coverage:
            coverage.add((state.platform.current.address, state.platform.current.pc))

    def did_read_code(self, state, offset, size):
        with self.locked_context('code_data', set) as code_data:
            for i in range(offset, offset+size):
                code_data.add((state.platform.current.address, i))


    def report(self, state_id):
        if state_id == -1:
            state = self.initial_state
        else:
            state = self._executor._workspace.load_state(state_id, delete=False)
        e = state.context['last_exception']
        world = state.platform
        def compare_buffers(a, b):
            if len(a) != len(b):
                return False
            cond = True
            for i in range(len(a)):
                cond = Operators.AND(a[i]==b[i], cond)
                if cond is False:
                    return False
            return cond

        print "="*20
        print "REPORT:", e, "\n"

        print "LOGS:"
        for address, memlog, topics in state.platform.logs:
            try:
                print  "\t", hex(state.solve_one(address)), repr(state.solve_one(memlog)), topics
            except Exception,e:
                print  "\t", address,  repr(memlog), topics

        #print state.constraints
        print "INPUT SYMBOLS"
        for expr in state.input_symbols:
            res = state.solve_one(expr)
            if isinstance(expr, Array):
                state.constrain(compare_buffers(expr, res))
            else:
                state.constrain(expr== res)
   
            try:
                print "\t", expr.name+':',  res.encode('hex')
            except:
                print "\t", expr.name+':',  res

        print "BALANCES"
        for address, account in world.storage.items():
            if issymbolic(account['balance']):
                m,M = solver.minmax(world.constraints, account['balance'])
                if m==M:
                    print "\t", hex(address), M
                else:
                    print "\t", hex(address), "range:[%x, %x]"%(m,M)                
            else:
                print "\t", hex(address), account['balance']
            


    def coverage(self, account_address):
        #This will just pick one of the running states.
        #This assumes the code and the accounts are the same in all versions of the world
        world = self.get_world(self.running_state_ids[0])
        seen = self.context['coverage'] #.union( self.context.get('code_data', set()))
        runtime_bytecode = world.storage[account_address]['code']

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
        offset = 0
        count = 0
        total = 0
        for i in evm.EVMDecoder.decode_all(runtime_bytecode) :
            
            if (account_address, offset) in seen:
                output += bcolors.OKGREEN
                output += "** 0x%04x %s\n"%(offset, i)
                output += bcolors.ENDC
                count += 1
            else:
                output += "   0x%04x %s\n"%(offset, i)
            
            total += 1
            offset += i.size

        output += "Total assembler lines: %d\n"% total
        output += "Total assembler lines visited: %d\n"% count
        output += "Coverage: %2.2f%%\n"%  (count*100.0/total)


        return output


    def symbolic_sha3(self, state, data, known_hashes):
        #print "SYMBOLIC HASH!"
        with self.locked_context('known_sha3', set) as known_sha3:
            state.platform._sha3.update(known_sha3)
        #print "symbolic_sha3", state, data, known_hashes
    def concrete_sha3(self, state, buf, value):
        #print "CONCRETE HASH!"
        with self.locked_context('known_sha3', set) as known_sha3:
            known_sha3.add((buf,value))
        #print "NEW KNOWN HASH", value

