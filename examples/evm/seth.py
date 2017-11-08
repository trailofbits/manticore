from manticore import Manticore
from manticore.core.smtlib import ConstraintSet, Operators, solver, issymbolic, Array, Expression, Constant
from manticore.core.smtlib.visitors import arithmetic_simplifier
from manticore.platforms import evm
from manticore.platforms.evm import pack_msb
from manticore.core.state import State
import tempfile
from subprocess import Popen, PIPE
import sha3
import json


class EVMContract(object):

    def __init__(self, address, seth=None, default_caller=None):
        self._default_caller = default_caller
        self._seth=seth
        self._address=address
        self._hashes = {}
        self._caller = None
        self._value = 0

        name, source_code, init_bytecode, metadata, metadata_runtime, hashes = self._seth.context['seth']['metadata'][address]
        for signature in hashes.keys():
            func_name = str(signature.split('(')[0])
            self._hashes[func_name] = signature, hashes[signature]

    def __int__(self):
        return self._address

    def value(self, value):
        self._value = value
        return self

    def caller(self, caller):
        self._caller = caller
        return self

    def __getattribute__(self, name):
        if not name.startswith('_') and name in self._hashes.keys():
            def f(*args, **kwargs):
                caller = kwargs.get('caller', self._caller)
                value = kwargs.get('value', self._value)
                tx_data = self._seth.make_function_call(str(self._hashes[name][0]),*args)
                if caller is not None:
                    caller = int(caller)
                else:
                    caller = self._default_caller
                self._seth.transaction(caller=caller,
                                        address=self._address,
                                        value=value,
                                        data=tx_data
                                     )
                self._caller = None
                self._value = 0
            return f
        else:
            return object.__getattribute__(self, name)            

class ManticoreEVM(Manticore):
    class SByte():
        def __init__(self, size=1):
            self.size=size
        def __mul__(self, reps):
            return Symbol(self.size*reps)
    SCHAR = SByte(1)
    SUINT = SByte(32)
    SValue = None
        

    @staticmethod
    def pack_msb(value):
        return ''.join(ManticoreEVM.serialize_uint(value))

    @staticmethod
    def serialize(value):
        if isinstance(value, (str,tuple)):
            return ManticoreEVM.serialize_string(value)
        if isinstance(value, (list)):
            return ManticoreEVM.serialize_array(value)
        if isinstance(value, (int, long)):
            return ManticoreEVM.serialize_uint(value)
        if isinstance(value, ManticoreEVM.SByte):
            return ManticoreEVM.serialize_uint(value.size) + (None,)*value.size + (('\x00',)*(32-(value.size%32)))
        if value is None:
            return (None,)*32


    @staticmethod
    def serialize_uint(value, size=32):
        '''takes an int and packs it into a 32 byte string, msb first''' 
        assert size >=1
        bytes = []
        for position in range(size):
            bytes.append( Operators.EXTRACT(value, position*8, 8) )
        chars = map(Operators.CHR, bytes)
        return tuple(reversed(chars))

    @staticmethod
    def serialize_string(value):
        assert isinstance(value, (str,tuple))
        return ManticoreEVM.serialize_uint(len(value)) + tuple(value) + tuple('\x00'*(32-(len(value)%32)))

    @staticmethod
    def serialize_array(value):
        assert isinstance(value, list)
        serialized = [ManticoreEVM.serialize_uint(len(value))]
        for item in value:
            serialized.append(ManticoreEVM.serialize(item))    
        return reduce(lambda x,y: x+y, serialized)

    @staticmethod
    def make_function_id( method_name):
        s = sha3.keccak_256()
        s.update(method_name)
        return s.hexdigest()[:8].decode('hex')

    @staticmethod
    def make_function_arguments(*args):
        
        if len(args) == 0:
            return () 
        args = list(args)
        for i in range(len(args)):
            if isinstance(args[i], EVMContract):
                 args[i] = int(args[i])
        result = []
        dynamic_args = []
        dynamic_offset = 32*len(args)
        for arg in args:
            if isinstance(arg, (list, tuple, str, ManticoreEVM.SByte)):
                result.append(ManticoreEVM.serialize(dynamic_offset))
                serialized_arg = ManticoreEVM.serialize(arg)
                dynamic_args.append(serialized_arg)
                assert len(serialized_arg)%32 ==0
                dynamic_offset += len(serialized_arg)
            else:
                result.append(ManticoreEVM.serialize(arg))

        for arg in dynamic_args:
            result.append(arg)

        return reduce(lambda x,y: x+y, result)
        
    @staticmethod
    def make_function_call(method_name, *args):
        function_id = ManticoreEVM.make_function_id(method_name)
        def check_bitsize(value, size):
            if isinstance(value, BitVec):
                return value.size==size
            return (value & ~((1<<size)-1)) == 0
        assert len(function_id) == 4
        result = [tuple(function_id)]
        result.append(ManticoreEVM.make_function_arguments(*args))
        return reduce(lambda x,y: x+y, result)

    @staticmethod
    def compile(source_code):
        """
        Compile a solidity source code
        """
        solc = "solc"
        with tempfile.NamedTemporaryFile() as temp:
            temp.write(source_code)
            temp.flush()
            p = Popen([solc, '--combined-json', 'srcmap,srcmap-runtime,bin,hashes', temp.name], stdout=PIPE)
            outp = json.loads(p.stdout.read())
            assert len(outp['contracts']), "Only one contract by file supported"
            name, outp = outp['contracts'].items()[0]
            name = name.split(':')[1]
            bytecode = outp['bin'].decode('hex')
            srcmap = outp['srcmap'].split(';')
            srcmap_runtime = outp['srcmap-runtime'].split(';')
            hashes = outp['hashes']
            return name, source_code, bytecode, srcmap, srcmap_runtime, hashes

    def __init__(self):

        #Make the constraint store
        constraints = ConstraintSet()
        #make the ethereum world state
        world = evm.EVMWorld(constraints)
        initial_state = State(constraints, world)
        initial_state.context['tx'] = []
        super(ManticoreEVM, self).__init__(initial_state)


        #The following should go to manticore.context so we can use multiprocessing
        self.context['seth'] = {}
        self.context['seth']['trace'] = []
        self.context['seth']['metadata'] = {}
        self.context['seth']['_pending_transaction'] = None
        self.context['seth']['_saved_states'] = []
        self.context['seth']['_final_states'] = []

        self._executor.subscribe('did_load_state', self.load_state_callback)
        self._executor.subscribe('will_terminate_state', self.terminate_state_callback)
        self._executor.subscribe('will_execute_instruction', self.will_execute_instruction_callback)
        self._executor.subscribe('did_execute_instruction', self.did_execute_instruction_callback)
        self._executor.subscribe('did_read_code', self.did_read_code)
        self._executor.subscribe('on_symbolic_sha3', self.symbolic_sha3)
        self._executor.subscribe('on_concrete_sha3', self.concrete_sha3)

    @property
    def world(self):
        if self.initial_state is None:
            return None
        return self.initial_state.platform

    @property
    def running_state_ids(self):
        with self.locked_context('seth') as context:
            if self.initial_state is not None:
                return context['_saved_states'] + [-1]
            else:
                return context['_saved_states']

    @property
    def final_state_ids(self):
        with self.locked_context('seth') as context:
            return context['_final_states']

    def get_world(self, state_id=-1):
        if state_id == -1:
            return self.initial_state.platform

        state = self._executor._workspace.load_state(state_id, delete=False)
        return state.platform

    def get_balance(self, address):
        if isinstance(address, EVMContract):
            address = int(address)
        return self.get_world().storage[address]['balance']

    def solidity_create_contract(self, source_code, owner, balance=0, address=None, args=()):
        name, source_code, init_bytecode, metadata, metadata_runtime, hashes = self.compile(source_code)
        address = self.create_contract(owner=owner, address=address, balance=balance, init=tuple(init_bytecode)+tuple(ManticoreEVM.make_function_arguments(*args)))
        self.context['seth']['metadata'][address] = name, source_code, init_bytecode, metadata, metadata_runtime, hashes
        return EVMContract(address, self, default_caller=owner)

    def create_contract(self, owner, balance=0, init=None, address=None):
        ''' Only available when there is a single state of the world'''
        with self.locked_context('seth') as context:
            assert context['_pending_transaction'] is None
        assert init is not None
        if address is None:
            address = self.world._new_address()
        self.context['seth']['_pending_transaction'] = ('CREATE_CONTRACT', owner, address, balance, init)

        self.run()

        return address

    def create_account(self, balance=0, address=None, code=''):
        ''' Only available when there is a single state of the world'''
        with self.locked_context('seth') as context:
           assert context['_pending_transaction'] is None
        return self.world.create_account( address, balance, code=code, storage=None)

    def transaction(self, caller, address, value, data):
        if isinstance(address, EVMContract):
            address = int(address)
        if isinstance(caller, EVMContract):
            caller = int(caller)


        if isinstance(data, self.SByte):
            data = (None,)*data.size
        with self.locked_context('seth') as context:
            context['_pending_transaction'] = ('CALL', caller, address, value, data)
        return self.run()

    def run(self, **kwargs):
        #Check if there is a pending transaction
        with self.locked_context('seth') as context:
            assert context['_pending_transaction'] is not None
            #there is at least one states in seth saved states
            assert context['_saved_states'] or self.initial_state

            #there is no states added to the executor queue
            assert len(self._executor.list()) == 0

            for state_id in context['_saved_states']:
                self._executor.put(state_id)
    
            context['_saved_states'] = []

        #A callback will use _pending_transaction and issue the transaction 
        #in each state (see load_state_callback)
        result = super(ManticoreEVM, self).run(**kwargs)

        with self.locked_context('seth') as context:
            if len(context['_saved_states'])==1:
                self._initial_state = self._executor._workspace.load_state(context['_saved_states'][0], delete=True)
                context['_saved_states'] = []

            #clear pending transcations. We are done.
            context['_pending_transaction'] = None
        return result
          
    def save(self, state, final=False):
        #save the state to secondary storage
        state_id = self._executor._workspace.save_state(state)

        with self.locked_context('seth') as context:
            if final:
                #Keep it on a private list
                context['_final_states'].append(state_id)
            else:
                #Keep it on a private list
                context['_saved_states'].append(state_id)
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
                with self.locked_context('seth') as context:
                    ty, caller, address, value, data = context['_pending_transaction']
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
        with self.locked_context('seth') as context:
            ty, caller, address, value, data = context['_pending_transaction']
            txnum = len(state.context['tx'])
        #Replace any none by symbolic values
        if value is None:
            value = state.new_symbolic_value(256, label='tx%d_value'%txnum)
        if isinstance (data, tuple):
            if any( x is None for x in data):
                symbolic_data = state.new_symbolic_buffer(label='tx%d_data'%txnum, nbytes=len(data))
                for i in range(len(data)):
                    if data[i] is not None:
                        symbolic_data[i] = data[i]
                data = symbolic_data
        state.context['tx'].append((ty, caller, address, value, data))


        if ty == 'CALL':
            world.transaction(address=address, caller=caller, data=data, value=value)
        else:
            assert ty == 'CREATE_CONTRACT'
            world.create_contract(caller=caller, address=address, balance=value, init=data)

    def will_execute_instruction_callback(self, state, instruction):
        assert state.constraints == state.platform.constraints
        assert state.platform.constraints == state.platform.current.constraints
        print  state.platform.current

        with self.locked_context('coverage', set) as coverage:
            coverage.add((state.platform.current.address, state.platform.current.pc))

    def did_execute_instruction_callback(self, state, prev_pc, pc, instruction):
        state.context.setdefault('seth.trace',[]).append((state.platform.current.address, pc))

    def did_read_code(self, state, offset, size):
        with self.locked_context('code_data', set) as code_data:
            for i in range(offset, offset+size):
                code_data.add((state.platform.current.address, i))


    def last_return(self, state_id=-1):
        if state_id == -1:
            state = self.initial_state
        else:
            state = self._executor._workspace.load_state(state_id, delete=False)
        return state.world.last_return


    def report(self, state_id, ty=None):
        def compare_buffers(a, b):
            if len(a) != len(b):
                return False
            cond = True
            for i in range(len(a)):
                cond = Operators.AND(a[i]==b[i], cond)
                if cond is False:
                    return False
            return cond

        if state_id == -1:
            state = self.initial_state
        else:
            state = self._executor._workspace.load_state(state_id, delete=False)

        world = state.platform
        trace = state.context['seth.trace']
        last_pc = trace[-1][1]
        last_address = trace[-1][0]
        try:
            md_name, md_source_code, md_init_bytecode, md_metadata, md_metadata_runtime, md_hashes= self.context['seth']['metadata'][last_address]
        except:
            md_name, md_source_code, md_init_bytecode, md_metadata, md_metadata_runtime, md_hashes = None,None,None,None,None,None 


        try:
            runtime_bytecode = world.storage[last_address]['code']
        except:
            runtime_bytecode = ''   

        e = state.context['last_exception']
        if ty is not None:
            if str(e) != ty:
                return
        print "="*20
        print "REPORT:", e, 

        try:
            asm = list(evm.EVMDecoder.decode_all(runtime_bytecode[:-9-33-2]))
            asm_offset = 0
            pos = 0
            source_pos = md_metadata_runtime[pos]
            for i in asm:
                if len(md_metadata_runtime[pos]):
                    source_pos = md_metadata_runtime[pos]
                if asm_offset == last_pc:
                    break
                asm_offset += i.size
                pos +=1

            beg, size = map(int, source_pos.split(':'))

            print " at:"
            nl = md_source_code.count('\n')
            snippet = md_source_code[beg:beg+size]
            for l in snippet.split('\n'):
                print '    ',nl,'  ', l
                nl+=1
        except:
            print

        print "BALANCES"
        for address, account in world.storage.items():
            if isinstance(account['balance'], Constant):
                account['balance'] = account['balance'].value

            if issymbolic(account['balance']):
                m, M = solver.minmax(world.constraints, arithmetic_simplifier(account['balance']))
                if m == M:
                    print "\t", hex(address), M
                else:
                    print "\t", hex(address), "range:[%x, %x]"%(m,M)                
            else:
                print "\t", hex(address), account['balance'],"wei"


        if state.platform.logs:
            print "LOGS:"
        for address, memlog, topics in state.platform.logs:
            try:
                res = memlog
                if isinstance(memlog, Expression):
                    res = state.solve_one(memlog)
                    if isinstance(memlog, Array):
                        state.constrain(compare_buffers(memlog, res))
                    else:
                        state.constrain(memlog== res)

                res1 = address
                if isinstance(address, Expression):
                    res = state.solve_one(address)
                    if isinstance(address, Array):
                        state.constrain(compare_buffers(address, res))
                    else:
                        state.constrain(address == res)

                print  "\t %s: %r %s" %( hex(res1), ''.join(map(chr,res)), topics)
            except Exception,e:
                print e
                print  "\t", address,  repr(memlog), topics

        print "INPUT SYMBOLS"
        for expr in state.input_symbols:
            res = state.solve_one(expr)
            if isinstance(expr, Array):
                state.constrain(compare_buffers(expr, res))
            else:
                state.constrain(expr== res)
   
            try:
                print "\t %s: %s"%( expr.name, res.encode('hex'))
            except:
                print "\t", expr.name+':',  res
        
        #print "Constraints:"
        #print state.constraints

        tx = state.context['tx']
        def x(expr):
            if issymbolic(expr):
                res = state.solve_one(expr)
                if isinstance(expr, Array):
                    state.constrain(compare_buffers(expr, res))
                else:
                    state.constrain(expr == res)
                expr=res
            if isinstance(expr, tuple):
                expr = ''.join(expr)
            return expr
        tx_num = 0
        for ty, caller, address, value, data in tx:
            tx_num += 1
            def consume_type(ty, data, offset):
                if ty == u'uint256':
                    return '0x'+data[offset:offset+64], offset+32*2
                elif ty == u'address':
                    return '0x'+data[offset+24:offset+64], offset+32*2
                elif ty == u'int256':
                    value = int('0x'+data[offset:offset+64],16)
                    mask = 2**(num_bits - 1)
                    value = -(value & mask) + (value & ~mask)
                    return value, offset+32*2
                elif ty == u'':
                    return '', offset
                elif ty in (u'bytes', u'string'):
                    dyn_offset = (4 + int('0x'+data[offset:offset+64],16))*2
                    size = int('0x'+data[dyn_offset:dyn_offset+64],16)
                    return data[dyn_offset+64:dyn_offset+64+size*2],offset+8
                else:
                    print "<",ty,">"
                    raise NotImplemented

            print "TRANSACTION ", tx_num, '-', ty
            try:
                md_name, md_source_code, md_init_bytecode, md_metadata, md_metadata_runtime, md_hashes= self.context['seth']['metadata'][address]
            except:
                md_name, md_source_code, md_init_bytecode, md_metadata, md_metadata_runtime, md_hashes = None,None,None,None,None,None 


            print '\t From: 0x%x'%x(caller)
            print '\t To: 0x%x'%x(address)
            print '\t Value: %d wei'%x(value)
            xdata = x(data).encode('hex')
            print '\t Data:', xdata
            if ty == 'CALL':
                print '\t Function: ', 
                done = False
                rhashes = dict((hsh, signature) for signature, hsh in md_hashes.iteritems())
                try:
                    signature = rhashes.get(xdata[:8], '{fallback}()')
                    done = True
                    func_name = signature.split('(')[0]
                    print func_name,'(',
                    types = signature.split('(')[1][:-1].split(',')
                    off = 8
                    for ty in types:
                        if off != 8:
                            print ',',
                        val, off = consume_type(ty, xdata, off)
                        print val,
                    print ')'
                except Exception,e:
                    print e, xdata   

        
        
            


    def coverage(self, account_address):
        account_address = int(account_address)
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


        end = None
        if  ''.join(runtime_bytecode[-44: -34]) =='\x00\xa1\x65\x62\x7a\x7a\x72\x30\x58\x20' \
            and  ''.join(runtime_bytecode[-2:]) =='\x00\x29':
            end = -9-33-2


        output = ''
        offset = 0
        count = 0
        total = 0
        for i in evm.EVMDecoder.decode_all(runtime_bytecode[:end]) :
            
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
        with self.locked_context('known_sha3', set) as known_sha3:
            state.platform._sha3.update(known_sha3)

    def concrete_sha3(self, state, buf, value):
        with self.locked_context('known_sha3', set) as known_sha3:
            known_sha3.add((buf,value))

