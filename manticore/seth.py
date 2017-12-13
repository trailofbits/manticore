from . import Manticore
from .core.smtlib import ConstraintSet, Operators, solver, issymbolic, Array, Expression, Constant
from .core.smtlib.visitors import arithmetic_simplifier
from .platforms import evm
from .core.state import State
import tempfile
from subprocess import Popen, PIPE
import sha3
import json
import logging
import StringIO
import cPickle as pickle
from .core.plugin import Plugin

logger = logging.getLogger(__name__)

################ Detectors ####################
class Detector(Plugin):
    @property
    def name(self):
        return self.__class__.__name__.split('.')[-1]

    def get_findings(self, state):
        return state.context.setdefault('seth.findings.%s'%self.name,set())

    def add_finding(self, state, finding):
        address = state.platform.current.address
        pc = state.platform.current.pc
        self.get_findings(state).add((address, pc, finding))

        with self.manticore.locked_context('seth.global_findings', set) as global_findings:
            global_findings.add((address, pc, finding))
        logger.info(finding)

    def _get_src(self, address, pc):
        return self.manticore.get_metadata(address).get_source_for(pc)

    def report(self, state):
        output = ''
        for address, pc, finding in self.get_findings(state):
            output += 'Finding %s\n' % finding
            output += '\t Contract: %s\n' % address
            output += '\t Program counter: %s\n' % pc
            output += '\t Snippet:\n'
            output += '\n'.join(('\t\t'+x for x in self._get_src(address, pc).split('\n')))
            output += '\n'
        return output


class IntegerOverflow(Detector):
    '''
        Detects any it overflow on instructions ADD and SUB.
    '''
    def did_evm_execute_instruction_callback(self, state, instruction, arguments, result):
        if instruction.semantics == 'ADD':
            if state.can_be_true(result < arguments[0]) or state.can_be_true(result < arguments[1]):
                self.add_finding(state, "Integer overflow at ADD instruction")
        if instruction.semantics == 'SUB':
            if state.can_be_true(arguments[1] > arguments[0]):
                src = self._get_src(state)
                self.add_finding(state, "Integer underflow at SUB instruction")
            
class UnitializedMemory(Detector):
    '''
        detects the use of not initialized memory
    '''
    def did_evm_read_memory(self, state, offset, value):
        if not state.can_be_true(value != 0):
            #Not initialized memory should be zero
            return 
        #check if offset is known
        cbu = True #Can be unknown
        for known_address in state.context['seth.detectors.initialized_memory']:
            cbu = Operators.AND(cbu, offset!=known_address)

        if state.can_be_true(cbu):
            self.add_finding(state, "Potentially reading uninitialized memory at instruction")
 
    def did_evm_write_memory(self, state, offset, value):
        #concrete or symbolic write
        state.context.setdefault('seth.detectors.initialized_memory',set()).add(offset)


class UnitializedStorage(Detector):
    '''
        UnitializedStorage: detects the use of not initialized storage
    '''
    def did_evm_read_storage(self, state, offset, value):
        if not state.can_be_true(value != 0):
            #Not initialized memory should be zero
            return 
        #check if offset is known
        cbu = True #Can be unknown
        for known_address in state.context['seth.detectors.initialized_storage']:
            cbu = Operators.AND(cbu, offset!=known_address)

        if state.can_be_true(cbu):
            self.add_finding(state, "Potentially reading uninitialized storage")
 
    def did_evm_write_storage(self, state, offset, value):
        #concrete or symbolic write
        state.context.setdefault('seth.detectors.initialized_storage',set()).add(offset)


def calculate_coverage(code, seen):
    '''     '''
    runtime_bytecode = code
    end = None
    if  ''.join(runtime_bytecode[-44: -34]) =='\x00\xa1\x65\x62\x7a\x7a\x72\x30\x58\x20' \
        and  ''.join(runtime_bytecode[-2:]) =='\x00\x29':
        end = -9-33-2  #Size of metadata at the end of most contracts

    count, total = 0, 0
    for i in evm.EVMAsm.disassemble_all(runtime_bytecode[:end]) :
        if i.offset in seen:
            count += 1            
        total += 1

    return count*100.0/total

class SolidityMetadata(object):
<<<<<<< HEAD
    def __build_source_map(self, bytecode, srcmap):
        # https://solidity.readthedocs.io/en/develop/miscellaneous.html#source-mappings
        new_srcmap = {}
        end = None
        if  ''.join(bytecode[-44: -34]) =='\x00\xa1\x65\x62\x7a\x7a\x72\x30\x58\x20' \
            and  ''.join(bytecode[-2:]) =='\x00\x29':
            end = -9-33-2  #Size of metadata at the end of most contracts

        asm_offset = 0
        asm_pos = 0
        md = dict(enumerate(srcmap[asm_pos].split(':')))
        s = int(md.get(0,0))
        l = int(md.get(1,0))
        f = int(md.get(2,0))
        j = md.get(3,None)

        for i in evm.EVMAsm.disassemble_all(bytecode[:end]):
            if asm_pos in srcmap and len(srcmap[asm_pos]):
                md = srcmap[asm_pos]
                if len(md):
                    d = {}
                    for p, k in enumerate(md.split(':')):
                        if len(k):
                            d[p]=k
                            
                    s = int(d.get(0,s))
                    l = int(d.get(1,l))
                    f = int(d.get(2,f))
                    j = d.get(3,j)

            new_srcmap[asm_offset] = (s,l,f,j)
            asm_pos += 1
            asm_offset += i.size

        return new_srcmap 


    def __init__(self, name, source_code, init_bytecode, runtime_bytecode, srcmap, srcmap_runtime, hashes, abi):
        self.name = name
        self.source_code = source_code
        self.init_bytecode = init_bytecode
        self.hashes = hashes
        self.abi = dict( [(item.get('name', '{fallback}'), item) for item in abi ])
        self.runtime_bytecode = runtime_bytecode
        self.srcmap_runtime = self.__build_source_map(runtime_bytecode, srcmap_runtime)
        self.srcmap = self.__build_source_map(init_bytecode, srcmap)

    def get_source_for(self, asm_offset, runtime=True):
        ''' Solidity source code snippet related to `asm_pos` evm bytecode offset
            if runtime is False it uses initialization bytecode source map
        '''
        if runtime:
            srcmap = self.srcmap_runtime
        else:
            srcmap = self.srcmap
        
        beg, size, _, _ = srcmap[asm_offset]
=======
    def __init__(self, name, source_code, init_bytecode, runtime_bytecode, metadata, metadata_runtime, hashes, abi):
        self.name = name
        self.source_code = source_code
        self.init_bytecode = init_bytecode
        self.metadata = metadata

        self.hashes = hashes
        self.abi = dict( [(item.get('name', '{fallback}'), item) for item in abi ])
        self.runtime_bytecode = runtime_bytecode

        # https://solidity.readthedocs.io/en/develop/miscellaneous.html#source-mappings
        self.metadata_runtime = {}
        end = None
        if  ''.join(runtime_bytecode[-44: -34]) =='\x00\xa1\x65\x62\x7a\x7a\x72\x30\x58\x20' \
            and  ''.join(runtime_bytecode[-2:]) =='\x00\x29':
            end = -9-33-2  #Size of metadata at the end of most contracts

        asm_offset = 0
        asm_pos = 0
        md = dict(enumerate(metadata_runtime[asm_pos].split(':')))
        s = int(md.get(0,0))
        l = int(md.get(1,0))
        f = int(md.get(2,0))
        j = md.get(3,None)

        for i in evm.EVMAsm.disassemble_all(self.runtime_bytecode[:end]):
            if len(metadata_runtime[asm_pos]):
                md = metadata_runtime[asm_pos]
                if len(md):
                    d = {}
                    for p, k in enumerate(md.split(':')):
                        if len(k):
                            d[p]=k
                            
                    s = int(d.get(0,s))
                    l = int(d.get(1,l))
                    f = int(d.get(2,f))
                    j = d.get(3,j)

            self.metadata_runtime[asm_offset] = (s,l,f,j)
            asm_pos += 1
            asm_offset += i.size

    def get_source_for(self, asm_pos):
        ''' Solidity source code snippet related to `asm_pos` evm bytecode offset
        '''
        beg, size, _, _ = self.metadata_runtime[asm_pos]
>>>>>>> master
        output = ''
        nl = self.source_code.count('\n')
        snippet = self.source_code[beg:beg+size]
        for l in snippet.split('\n'):
            output += '    %s  %s\n'%(nl, l)
            nl+=1
        return output

    @property
    def signatures(self):
        return dict(( (b,a) for (a,b) in self.hashes.items() ))

    def get_abi(self, hsh):
        func_name = self.get_func_name(hsh)
        return self.abi[func_name]

    def get_func_argument_types(self, hsh):
        abi = self.get_abi(hsh)
        return '('+','.join(x['type'] for x in abi['inputs']) +')'

    def get_func_return_types(self, hsh):
        abi = self.get_abi(hsh)
        return '('+','.join(x['type'] for x in abi['outputs']) +')'

    def get_func_name(self, hsh):
        signature = self.signatures.get(hsh,'{fallback}()')
        return signature.split('(')[0]
        
    def get_func_signature(self, hsh):
        return self.signatures.get(hsh, '{fallback}()')

class ABI(object):
    '''
        This class contains methods to handle the ABI.
        The Application Binary Interface is the standard way to interact with
        contracts in the Ethereum ecosystem, both from outside the blockchain 
        and for contract-to-contract interaction. 

    '''
    class SByte():
        ''' Unconstrained symbolic byte, not asociated with any constraint set '''
        def __init__(self, size=1):
            self.size=size
        def __mul__(self, reps):
            return Symbol(self.size*reps)

    SCHAR = SByte(1)
    SUINT = SByte(32)
    SValue = None

    @staticmethod
    def serialize(value):
        ''' Translates a python object to its EVM ABI serialization.
            It supports s '''
        if isinstance(value, (str,tuple)):
            return ABI.serialize_string(value)
        if isinstance(value, (list)):
            return ABI.serialize_array(value)
        if isinstance(value, (int, long)):
            return ABI.serialize_uint(value)
        if isinstance(value, ABI.SByte):
            return ABI.serialize_uint(value.size) + (None,)*value.size + (('\x00',)*(32-(value.size%32)))
        if value is None:
            return (None,)*32

    @staticmethod
    def serialize_uint(value, size=32):
        '''Translates a python int into a 32 byte string, msb first''' 
        assert size >=1
        bytes = []
        for position in range(size):
            bytes.append( Operators.EXTRACT(value, position*8, 8) )
        chars = map(Operators.CHR, bytes)
        return tuple(reversed(chars))

    @staticmethod
    def serialize_string(value):
        '''Translates a string or a tuple of chars its EVM ABI serialization''' 
        assert isinstance(value, (str,tuple))
        return ABI.serialize_uint(len(value)) + tuple(value) + tuple('\x00'*(32-(len(value)%32)))

    @staticmethod
    def serialize_array(value):
        assert isinstance(value, list)
        serialized = [ABI.serialize_uint(len(value))]
        for item in value:
            serialized.append(ABI.serialize(item))    
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
            if isinstance(args[i], EVMAccount):
                 args[i] = int(args[i])
        result = []
        dynamic_args = []
        dynamic_offset = 32*len(args)
        for arg in args:
            if isinstance(arg, (list, tuple, str, ManticoreEVM.SByte)):
                result.append(ABI.serialize(dynamic_offset))
                serialized_arg = ABI.serialize(arg)
                dynamic_args.append(serialized_arg)
                assert len(serialized_arg)%32 ==0
                dynamic_offset += len(serialized_arg)
            else:
                result.append(ABI.serialize(arg))

        for arg in dynamic_args:
            result.append(arg)

        return reduce(lambda x,y: x+y, result)
        
    @staticmethod
    def make_function_call(method_name, *args):
        function_id = ABI.make_function_id(method_name)
        def check_bitsize(value, size):
            if isinstance(value, BitVec):
                return value.size==size
            return (value & ~((1<<size)-1)) == 0
        assert len(function_id) == 4
        result = [tuple(function_id)]
        result.append(ABI.make_function_arguments(*args))
        return reduce(lambda x,y: x+y, result)



    @staticmethod        
    def _consume_type(ty, data, offset):
        def get_uint(size, offset):
            byte_size = size/8
            padding = 32 - byte_size # for 160
            return Operators.CONCAT(size, *map(Operators.ORD, data[offset+padding:offset+padding+byte_size]))
        if ty == u'uint256':
            return get_uint(256, offset), offset+32
        if ty == u'bool':
            return get_uint(8, offset), offset+32
        elif ty == u'address':
            return get_uint(160, offset), offset+32
        elif ty == u'int256':
            value = get_uint(256, offset)
            mask = 2**(256 - 1)
            value = -(value & mask) + (value & ~mask)
            return value, offset+32
        elif ty == u'':
            return None, offset
        elif ty in (u'bytes', u'string'):
            dyn_offset = 4 + get_uint(256,offset)
            size = get_uint(256, dyn_offset)
            return data[dyn_offset+32:dyn_offset+32+size], offset+4
        else:
            print "<",ty,">"
            raise NotImplemented(ty)

    @staticmethod
    def parse(signature, data):
        is_multiple = '(' in signature

        if is_multiple:
            func_name = signature.split('(')[0]
            types = signature.split('(')[1][:-1].split(',')
            if len(func_name) > 0:
                off = 4
            else:
                func_name = None
                off = 0
        else:
            func_name = None
            types = (signature,)
            off = 0

        arguments = []
        for ty in types:
            val, off = ABI._consume_type(ty, data, off)
            if val is not None:
                arguments.append(val)
            else:
                break

        if is_multiple:
            if func_name is not None:
                return func_name, tuple(arguments)
            else:
                return tuple(arguments)
        else:
            return arguments[0]



class EVMAccount(object):
    ''' An EVM account '''
    def __init__(self, address, seth=None, default_caller=None):
        ''' Encapsulates an account. 

            :param address: the address of this account
            :type address: 160 bit long integer
            :param seth: the controlling manticore
            :param default_caller: the default caller address for any transaction

        '''
        self._default_caller = default_caller
        self._seth=seth
        self._address=address
        self._hashes = {}

        if self._seth:
            md = self._seth.get_metadata(address)
            if md is not None:
                for signature, func_id in md.hashes.items():
                    func_name = str(signature.split('(')[0])
                    self._hashes[func_name] = signature, func_id

    def __int__(self):
        return self._address

    def __str__(self):
        return str(self._address)

    def __getattribute__(self, name):
        ''' If this is a contract account of which we know the functions hashes
            this will build the transaction for the function call.

            Example use::
        
                #call funtion `add` on contract_account with argument `1000`
                contract_account.add(1000)
         
        '''
        if not name.startswith('_') and name in self._hashes.keys():
            def f(*args, **kwargs):
                caller = kwargs.get('caller', None)
                value = kwargs.get('value', 0)
                tx_data = ABI.make_function_call(str(self._hashes[name][0]), *args)
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
    ''' Manticore EVM manager
    
        Usage Ex::

            from manticore.seth import ManticoreEVM, ABI
            seth = ManticoreEVM()
            #And now make the contract account to analyze
            source_code = """
                pragma solidity ^0.4.15;
                contract AnInt {
                    uint private i=0;                    
                    function set(uint value){
                        i=value
                    } 
                }
            """
            #Initialize user and contracts
            user_account = seth.create_account(balance=1000)
            contract_account = seth.solidity_create_contract(source_code, owner=user_account, balance=0)
            contract_account.set(12345, value=100) 

            seth.report()
            print seth.coverage(contract_account)
    '''
    SByte=ABI.SByte
    SValue=ABI.SValue

    def make_symbolic_buffer(self, size):
        ''' Creates a symbolic buffer of size bytes to be used in transactions.
            You can not operate on it. It is intended as a place holder for the 
            real expression.
            
            Example use::
                
                symbolic_data = seth.make_symbolic_buffer(320)
                seth.transaction(caller=attacker_account,
                                address=contract_account,
                                data=symbolic_data,
                                value=100000 )


        '''
        return ABI.SByte(size)

    def make_symbolic_value(self):
        ''' Creates a symbolic value, normally a uint256, to be used in transactions.
            You can not operate on it. It is intended as a place holder for the 
            real expression.
            
            Example use::
                
                symbolic_value = seth.make_symbolic_value()
                seth.transaction(caller=attacker_account,
                                address=contract_account,
                                data=data,
                                value=symbolic_data )

        '''
        return ABI.SValue

    @staticmethod
    def compile(source_code):
        ''' Get initialization bytecode from a solidity source code '''
        name, source_code, bytecode, srcmap, srcmap_runtime, hashes, abi = ManticoreEVM._compile(source_code)
        return bytecode

    @staticmethod
    def _compile(source_code):
        """ Compile a solidity contract, used internally
            
            :param source_code: a solidity source code
            :return: name, source_code, bytecode, srcmap, srcmap_runtime, hashes
        """
        solc = "solc"
        with tempfile.NamedTemporaryFile() as temp:
            temp.write(source_code)
            temp.flush()
            p = Popen([solc, '--combined-json', 'abi,srcmap,srcmap-runtime,bin,hashes,bin-runtime', temp.name], stdout=PIPE)
            outp = json.loads(p.stdout.read())
            assert len(outp['contracts']), "Only one contract by file supported"
            name, outp = outp['contracts'].items()[0]
            name = name.split(':')[1]
            bytecode = outp['bin'].decode('hex')
            srcmap = outp['srcmap'].split(';')
            srcmap_runtime = outp['srcmap-runtime'].split(';')
            hashes = outp['hashes']
            abi = json.loads(outp['abi'])
            runtime = outp['bin-runtime'].decode('hex')
            return name, source_code, bytecode, runtime, srcmap, srcmap_runtime, hashes, abi

    def __init__(self, procs=1):
        ''' A manticere EVM manager 
            :param procs: number of workers to use in the exploration  
        '''
        self.normal_accounts = set()
        self.contract_accounts = set()
        self._config_procs=procs
        #Make the constraint store
        constraints = ConstraintSet()
        #make the ethereum world state
        world = evm.EVMWorld(constraints)
        initial_state = State(constraints, world)
        initial_state.context['tx'] = []
        super(ManticoreEVM, self).__init__(initial_state)

        self.detectors = {}
        self.metadata = {}

        #The following should go to manticore.context so we can use multiprocessing
        self.context['seth'] = {}
        self.context['seth']['_pending_transaction'] = None
        self.context['seth']['_saved_states'] = []
        self.context['seth']['_final_states'] = []

        self._executor.subscribe('did_load_state', self._load_state_callback)
        self._executor.subscribe('will_terminate_state', self._terminate_state_callback)
        self._executor.subscribe('will_execute_instruction', self._will_execute_instruction_callback)
        self._executor.subscribe('did_execute_instruction', self._did_execute_instruction_callback)
        self._executor.subscribe('did_read_code', self._did_evm_read_code)
        self._executor.subscribe('on_symbolic_sha3', self._symbolic_sha3)
        self._executor.subscribe('on_concrete_sha3', self._concrete_sha3)

    @property
    def world(self):
        ''' The world instance or None if there is more than one state '''  
        return self.get_world(None)

    @property
    def running_state_ids(self):
        ''' IDs of the running states''' 
        with self.locked_context('seth') as context:
            if self.initial_state is not None:
                return context['_saved_states'] + [-1]
            else:
                return context['_saved_states']


    @property
    def all_state_ids(self):
        ''' IDs of the all states ''' 
        return self.running_state_ids + self.terminated_state_ids

    @property
    def terminated_state_ids(self):
        ''' IDs of the terminated states ''' 
        with self.locked_context('seth') as context:
            return context['_final_states']

    @property
    def running_states(self):
        ''' Iterates over the running states''' 
        for state_id in self.running_state_ids:
            state = self.load(state_id)
            yield state

    @property
    def terminated_states(self):
        ''' Iterates over the terminated states''' 
        for state_id in self.terminated_state_ids:
            state = self.load(state_id)
            yield state

    @property
    def all_states(self):
        ''' Iterates over the all states (terminated and alive)''' 
        for state_id in self.terminated_state_ids + self.running_state_ids:
            state = self.load(state_id)
            yield state

    def terminate_state_id(self, state_id):
        with self.locked_context('seth') as seth_context:
            lst = seth_context['_saved_states']
            lst.remove(state_id)
            seth_context['_saved_states'] = lst

        state = self.load(state_id)
        self._generate_testcase_callback(state, 'test', 'Still Running')

        with self.locked_context('seth') as seth_context:
            lst = seth_context['_final_states']
            lst.append(state_id)
            seth_context['_final_states'] = lst
        

    #deprecate this 5 in favor of for sta in seth.all_states: do stuff?
    def get_world(self, state_id=None):
        ''' Returns the evm world of `state_id` state. '''
        state = self.load(state_id)
        if state is None:
            return None
        else:
            return state.platform

    def get_balance(self, address, state_id=None):
        ''' Balance for account `address` on state `state_id` '''
        if isinstance(address, EVMAccount):
            address = int(address)
        return self.get_world(state_id).storage[address]['balance']

    def get_storage(self, address, offset, state_id=None):
        ''' Storage data for `offset` on account `address` on state `state_id` '''
        if isinstance(address, EVMAccount):
            address = int(address)
        return self.get_world(state_id).storage[address]['storage'].get(offset)

    def last_return(self, state_id=None):
        ''' Last returned buffer for state `state_id` '''
        state = self.load(state_id)
        return state.platform.last_return

    def transactions(self, state_id=None):
        ''' Transactions list for state `state_id` '''
        state = self.load(state_id)
        return state.platform.transactions

    def solidity_create_contract(self, source_code, owner, balance=0, address=None, args=()):
        ''' Creates a solidity contract 

            :param source_code: solidity source code
            :type source_code: str
            :param owner: owner account (will be default caller in any transactions)
            :type owner: int or EVMAccount
            :param balance: balance to be transfered on creation
            :type balance: int or SValue
            :param address: the address for the new contract (optional)
            :type address: int or EVMAccount
            :param args: constructor arguments
            :type args: tuple
            :return: an EVMAccount
        '''

        name, source_code, init_bytecode, runtime_bytecode, metadata, metadata_runtime, hashes, abi = self._compile(source_code)
        address = self.create_contract(owner=owner, address=address, balance=balance, init=tuple(init_bytecode)+tuple(ABI.make_function_arguments(*args)))
        self.metadata[address] = SolidityMetadata(name, source_code, init_bytecode, runtime_bytecode, metadata, metadata_runtime, hashes, abi)
        return EVMAccount(address, self, default_caller=owner)

    def create_contract(self, owner, balance=0, init=None, address=None):
        ''' Creates a contract 

            :param init: initializing evm bytecode and arguments
            :type init: str
            :param owner: owner account (will be default caller in any transactions)
            :type owner: int or EVMAccount
            :param balance: balance to be transfered on creation
            :type balance: int or SValue
            :param address: the address for the new contract (optional)
            :type address: int
            :return: an EVMAccount
        '''
        assert len(self.running_state_ids) == 1, "No forking yet"
        with self.locked_context('seth') as context:
            assert context['_pending_transaction'] is None
        assert init is not None
        if address is None:
            address = self.world._new_address()
        self.context['seth']['_pending_transaction'] = ('CREATE_CONTRACT', owner, address, balance, init)

        self.run(procs=self._config_procs)

        self.contract_accounts.add(address)
        return address

    def create_account(self, balance=0, address=None, code=''):
        ''' Creates a normal account

            :param balance: balance to be transfered on creation
            :type balance: int or SValue
            :param address: the address for the new contract (optional)
            :type address: int
            :return: an EVMAccount
        '''
        assert len(self.running_state_ids) == 1, "No forking yet"
        with self.locked_context('seth') as context:
           assert context['_pending_transaction'] is None
        address = self.world.create_account( address, balance, code=code, storage=None)
        self.normal_accounts.add(address)
        return address

    def transaction(self, caller, address, value, data):
        ''' Issue a transaction 

            :param caller: the address of the account sending the transaction
            :type caller: int or EVMAccount
            :param value: balance to be transfered on creation
            :type value: int or SValue
            :param address: the address of the contract to call
            :type address: int or EVMAccount
            :return: an EVMAccount
        '''
        if isinstance(address, EVMAccount):
            address = int(address)
        if isinstance(caller, EVMAccount):
            caller = int(caller)
        
        if isinstance(data, self.SByte):
            data = (None,)*data.size
        with self.locked_context('seth') as context:
            context['_pending_transaction'] = ('CALL', caller, address, value, data)
        return  self.run(procs=self._config_procs)

    def run(self, **kwargs):
        ''' Run any pending transaction on any running state '''

        #Check if there is a pending transaction
        with self.locked_context('seth') as context:
            assert context['_pending_transaction'] is not None
            #there is at least one states in seth saved states
            assert context['_saved_states'] or self.initial_state is not None
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
                assert self.running_state_ids == [-1]

            #clear pending transcations. We are done.
            context['_pending_transaction'] = None
        return result
          
    def save(self, state, final=False):
        ''' Save a state in secondary storage and add it to running or final lists

            :param state: A manticore State
            :param final: True if state is final
            :returns: a state id

        '''
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

    def load(self, state_id=None):
        ''' Load one of the running or final states.
            
            :param state_id: If None it assumes there is a single running state
            :type state_id: int or None
        '''
        state = None
        if state_id is None:
            #a single state was assumed
            if len(self.running_state_ids) == 1:  
                #Get the ID of the single running state              
                state_id = self.running_state_ids[0]
            else:
                raise Exception("More than one state running.")

        if state_id == -1:
            state = self.initial_state
        else:
            state = self._executor._workspace.load_state(state_id, delete=False)
        return state

    #Callbacks
    def _symbolic_sha3(self, state, data, known_hashes):
        ''' INTERNAL USE '''

        with self.locked_context('known_sha3', set) as known_sha3:
            state.platform._sha3.update(known_sha3)

    def _concrete_sha3(self, state, buf, value):
        ''' INTERNAL USE '''
        with self.locked_context('known_sha3', set) as known_sha3:
            known_sha3.add((buf,value))

    def _terminate_state_callback(self, state, state_id, e):
        ''' INTERNAL USE 
            Every time a state finishes executing last transaction we save it in
            our private list 
        '''
        state.context['last_exception'] = e
        # TODO(mark): This will break if we ever change the message text. Use a less
        # brittle check.
        if e.message not in {'REVERT', 'Not Enough Funds for transaction'}:
            # if not a revert we save the state for further transactioning
            state.context['processed'] = False
            if e.message == 'RETURN':
                with self.locked_context('seth') as context:
                    ty, caller, address, value, data = context['_pending_transaction']
                    if ty == 'CREATE_CONTRACT':
                        world = state.platform
                        world.storage[address]['code'] = world.last_return_data

            self.save(state)
            e.testcase = False  #Do not generate a testcase file
        else:
            self.save(state, final=True)



    #Callbacks
    def _load_state_callback(self, state, state_id):
        ''' INTERNAL USE 
            When a state was just loaded from stoage we do the pending transaction
        '''
        if state.context.get('processed', False):
            return
        world = state.platform
        state.context['processed'] = True
        with self.locked_context('seth') as context:
            #take current global transaction we need to apply to all running states
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
        if ty == 'CALL':
            world.transaction(address=address, caller=caller, data=data, value=value)
        else:
            assert ty == 'CREATE_CONTRACT'
            world.create_contract(caller=caller, address=address, balance=value, init=data)
        state.context['tx'].append((ty, caller, address, value, data))

    def _will_execute_instruction_callback(self, state, pc, instruction):
        ''' INTERNAL USE '''
        assert state.constraints == state.platform.constraints
        assert state.platform.constraints == state.platform.current.constraints
        #print state.platform.current
        with self.locked_context('coverage', set) as coverage:
            coverage.add((state.platform.current.address, state.platform.current.pc))
        
    def _did_execute_instruction_callback(self, state, prev_pc, pc, instruction):
        ''' INTERNAL USE '''
        state.context.setdefault('seth.trace',[]).append((state.platform.current.address, prev_pc))

    def _did_evm_read_code(self, state, offset, size):
        ''' INTERNAL USE '''
        with self.locked_context('code_data', set) as code_data:
            for i in range(offset, offset+size):
                code_data.add((state.platform.current.address, i))

    def get_metadata(self, address):
        ''' Gets the solidity metadata for address.
            This is available only if address is a contract created from solidity
        '''
        return self.metadata.get(address)

    def register_detector(self, d):
        if not isinstance(d, Detector):
            raise Exception("Not a Detector")
        self.detectors[d.name] = d
        self.register_plugin(d)

    @property
    def global_findings(self):
        with self.locked_context('seth.global_findings', set) as global_findings:
            return global_findings

    @property
    def workspace(self):
        return self._executor._workspace._store.uri

    def _generate_testcase_callback(self, state, name, message):
        '''
        Create a serialized description of a given state.
        :param state: The state to generate information about
        :param message: Accompanying message
        '''
        # workspace should not be responsible for formating the output
        # each object knows its secrets, each class should be able to report its
        # final state
        #super(ManticoreEVM, self)._generate_testcase_callback(state, name, message)
        def flagged(flag):
            return '(*)' if flag else '' 
        testcase = self._output.testcase()
        logger.info("Generated testcase No. {} - {}".format(testcase.num, message))
        blockchain = state.platform
        with testcase.open_stream('summary') as summary:            
            summary.write("Last exception: %s\n" %state.context['last_exception'])

            #Last instruction
            metadata = self.get_metadata(blockchain.transactions[-1].address)
            if metadata is not None:
                address, offset = state.context['seth.trace'][-1]
                summary.write('Last instruction at contract %x offset %x\n' %(address, offset))
                at_runtime = blockchain.transactions[-1].sort != 'Create'
                summary.write(metadata.get_source_for(offset, at_runtime))
                summary.write('\n')



            #Accounts summary
            is_something_symbolic = False
            summary.write("%d accounts.\n" % len(blockchain.accounts))
            for account_address in blockchain.accounts:
                summary.write("Address: 0x%x\n" % account_address)
                balance = blockchain.get_balance(account_address)
                is_balance_symbolic = issymbolic(balance)
                is_something_symbolic = is_something_symbolic or is_balance_symbolic
                balance = state.solve_one(balance)
                summary.write("Balance: %d %s\n" % (balance, flagged(is_balance_symbolic)))

                if blockchain.has_storage(account_address):
                    summary.write("Storage:\n")
                    for offset, value in blockchain.get_storage_items(account_address):
                        is_storage_symbolic = issymbolic(offset) or issymbolic(value) 
                        offset = state.solve_one(offset)
                        value = state.solve_one(value)
                        summary.write("\t%032x -> %032x %s\n" % (offset, value, flagged(is_storage_symbolic)))
                        is_something_symbolic = is_something_symbolic or is_storage_symbolic

                code = blockchain.get_code(account_address)
                if len(code):
                    summary.write("Code:\n")
                    fcode = StringIO.StringIO(code)
                    for chunk in iter(lambda: fcode.read(32), b''):
                        summary.write('\t%s\n' % chunk.encode('hex'))
                    trace = set(( offset for address_i, offset in state.context['seth.trace'] if address == address_i))        
                    summary.write("Coverage %d%% (on this state)\n" %  calculate_coverage(code, trace)) #coverage % for address in this account/state
                summary.write("\n")


            if is_something_symbolic:
                summary.write('\n\n(*) Example solution given. Value is symbolic and may take other values\n')


        #Transactions
        with testcase.open_stream('tx') as tx_summary:
            for tx in blockchain.transactions: #external transactions
                tx_summary.write("Transactions Nr. %d\n" % blockchain.transactions.index(tx))

                #The result if any RETURN or REVERT
                tx_summary.write("Type: %s -> %s\n" % (tx.sort, 'OK' if tx.result == 'RETURN' else 'FAIL' ))
                tx_summary.write("From: 0x%x %s\n" % (state.solve_one(tx.caller), flagged(issymbolic(tx.caller))))
                tx_summary.write("To: 0x%x %s\n" % (state.solve_one(tx.address), flagged(issymbolic(tx.address))))
                tx_summary.write("Value: %d %s\n"% (state.solve_one(tx.value), flagged(issymbolic(tx.value))))
                tx_summary.write("Data: %s %s\n"% (state.solve_one(tx.data).encode('hex'), flagged(issymbolic(tx.data))))
                if tx.return_data is not None:
                    return_data = state.solve_one(tx.return_data)
                    tx_summary.write("Return_data: %s %s\n" % (''.join(return_data).encode('hex'), flagged(issymbolic(tx.return_data))))

                
                metadata = self.get_metadata(tx.address)
                if tx.sort == 'Call':
                    if metadata is not None:
                        function_id = tx.data[:4]  #hope there is enough data
                        function_id = state.solve_one(function_id).encode('hex')
                        signature = metadata.get_func_signature(function_id)
                        function_name, arguments = ABI.parse(signature, tx.data)

                        if tx.result == 'RETURN':
                            ret_types = metadata.get_func_return_types(function_id)
                            return_data = ABI.parse(ret_types, tx.return_data) #function return

                        tx_summary.write('\n')
                        tx_summary.write( "Function call:\n")
                        tx_summary.write("%s(" % state.solve_one(function_name ))
                        tx_summary.write(','.join(map(str, map(state.solve_one, arguments))))
                        tx_summary.write(') -> %s\n' % tx.result)
                        tx_summary.write('return_data: %s\n' % ''.join(map(chr, map(state.solve_one, return_data))))

                tx_summary.write('\n\n')

        #logs
        with testcase.open_stream('logs') as logs_summary:
            #the logs
            for log_item in blockchain.logs:
                logs_summary.write("Address: %x\n" % log_item.address)
                logs_summary.write("Memlog: %s %s\n" % (state.solve_one(log_item.memlog).encode('hex'), flagged(issymbolic(log_item.memlog))))
                logs_summary.write("Topics:\n")
                for topic in log_item.topics:
                    logs_summary.write("\t%d) %x %s" %(log_item.topics.index(topic), state.solve_one(topic), flagged(issymbolic(topic))))
            else:
                logs_summary.write('No logs')

        with testcase.open_stream('constraints') as smt_summary:
            smt_summary.write(str(state.constraints))

        with testcase.open_stream('pkl') as statef:
            try:
                statef.write(pickle.dumps(state, 2))
            except RuntimeError:
                # recursion exceeded. try a slower, iterative solution
                from .utils import iterpickle
                logger.debug("Using iterpickle to dump state")
                statef.write(iterpickle.dumps(state, 2))



    def finalize(self):
        #move runnign states to final states list
        # and generate a testcase for each
        lst = tuple(self.running_state_ids)
        for state_id in lst:
            self.terminate_state_id(state_id)

        #delete actual streams from storage
        for state_id in self.all_state_ids:
            self._executor._workspace.rm_state(state_id)

        #clean up lists
        with self.locked_context('seth') as seth_context:
            seth_context['_saved_states'] = []
        with self.locked_context('seth') as seth_context:
            seth_context['_final_states'] = []
        
        #global summary
        with self._output.save_stream('global.summary') as global_summary :
            # (accounts created by contract code are not in this list )
            global_summary.write( "Global coverage:\n")
            for address in self.contract_accounts: 
                global_summary.write("%x: %d%%\n" % (address, self.global_coverage(address))) #coverage % for address in this state


            if len(self.global_findings):
                global_summary.write( "Global Findings:\n")

                for address, pc, finding in m.global_findings:
                    global_summary.write('- %s -\n' % finding )
                    global_summary.write( '\t Contract: %s\n' % address )
                    global_summary.write( '\t Program counter: %s\n' % pc )
                    md = self.get_metadata(address)
                    if md is not None:
                        src = md.get_source_for(pc)
                        global_summary.write( '\t Snippet:\n' )
                        global_summary.write( '\n'.join(('\t\t'+x for x in src.split('\n'))) )
                        global_summary.write( '\n\n' )


        logger.info("[+] Look for results in %s", self.workspace )


    def report(self, state, ty=None):
        ''' Prints a small report on state. Prints a little something about state :) '''
        world = state.platform

        output = StringIO.StringIO()

        def compare_buffers(a, b):
            if len(a) != len(b):
                return False
            cond = True
            for i in range(len(a)):
                cond = Operators.AND(a[i]==b[i], cond)
                if cond is False:
                    return False
            return cond

        trace = state.context['seth.trace']
        last_address, last_pc = trace[-1]        
        #Try to recover metadata from solidity based contracts
        try:
            md_name, md_source_code, md_init_bytecode, md_metadata, md_metadata_runtime, md_hashes = self.context['seth']['metadata'][last_address]
        except:
            md_name, md_source_code, md_init_bytecode, md_metadata, md_metadata_runtime, md_hashes = None, None, None, None, None, None 

        # try to get the runtime bytecode from the account
        try:
            runtime_bytecode = world.storage[last_address]['code']
        except:
            runtime_bytecode = ''   

        e = state.context['last_exception']
        if ty is not None:
            if str(e) != ty:
                return

        output.write("REPORT:" + str(e)) 

        try:
            # Magic number comes from here:
            # http://solidity.readthedocs.io/en/develop/metadata.html#encoding-of-the-metadata-hash-in-the-bytecode
            asm = list(evm.EVMAsm.disassemble_all(runtime_bytecode[:-9-33-2]))
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

            output.write( " at:" )
            nl = md_source_code.count('\n')
            snippet = md_source_code[beg:beg+size]
            for l in snippet.split('\n'):
                output.write('    %s  %s\n'%(nl, l))
                nl+=1
        except Exception as e:
            output.write('\n')

        output.write("BALANCES\n")
        for address, account in world.storage.items():
            if isinstance(account['balance'], Constant):
                account['balance'] = account['balance'].value

            if issymbolic(account['balance']):
                m, M = solver.minmax(world.constraints, arithmetic_simplifier(account['balance']))
                if m == M:
                    output.write('\t%x %r\n'%(address, M))
                else:
                    output.write('\t%x range:[%x, %x]\n'%(address, m, M))
            else:
                output.write('\t%x %d wei\n'%(address, account['balance']))

        if world.logs:
            output.write('LOGS:\n')
            for address, memlog, topics in world.logs:
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

                    output.write('\t %s: %r %s\n' %( hex(res1), ''.join(map(chr,res)), topics))
                except Exception,e:
                    output.write('\t %r %r %r\n' % (address,  repr(memlog), topics))

        output.write('INPUT SYMBOLS\n')
        for expr in state.input_symbols:
            res = state.solve_one(expr)
            if isinstance(expr, Array):
                state.constrain(compare_buffers(expr, res))
            else:
                state.constrain(expr== res)
   
            try:
                output.write('\t %s: %s\n'%( expr.name, res.encode('hex')))
            except:
                output.write('\t %s: %s\n'% (expr.name, res))
        
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
                    mask = 2**(256 - 1)
                    value = -(value & mask) + (value & ~mask)
                    return value, offset+32*2
                elif ty == u'':
                    return '', offset
                elif ty in (u'bytes', u'string'):
                    dyn_offset = (4 + int('0x'+data[offset:offset+64],16))*2
                    size = int('0x'+data[dyn_offset:dyn_offset+64],16)
                    return data[dyn_offset+64:dyn_offset+64+size*2],offset+8
                else:
                    raise NotImplemented(ty)

            output.write('TRANSACTION %d - %s' % (tx_num, ty))
            try:
                md_name, md_source_code, md_init_bytecode, md_metadata, md_metadata_runtime, md_hashes= self.context['seth']['metadata'][address]
            except:
                md_name, md_source_code, md_init_bytecode, md_metadata, md_metadata_runtime, md_hashes = None,None,None,None,None,None 


            output.write('\t From: 0x%x\n'% x(caller) )
            output.write('\t To: 0x%x\n'%x(address))
            output.write('\t Value: %d wei\n'%x(value))
            xdata = x(data).encode('hex')
            output.write('\t Data: %s\n'% xdata)
            if ty == 'CALL':
                done = False
                try:
                    rhashes = dict((hsh, signature) for signature, hsh in md_hashes.iteritems())
                    signature = rhashes.get(xdata[:8], '{fallback}()')
                    done = True
                    func_name = signature.split('(')[0]
                    output.write('\t Function: %s(' % func_name)
                    types = signature.split('(')[1][:-1].split(',')
                    off = 8
                    for ty in types:
                        if off != 8:
                            print ',',
                        val, off = consume_type(ty, xdata, off)
                        output.write('%s'%val)
                    output.write(')\n')
                except Exception,e:
                    output.write('%s %s\n'%(e, xdata))
        return output.getvalue()

    def global_coverage(self, account_address):
        ''' Returns code coverage for the contract on `account_address`.
            This sums up all the visited code lines from any of the explored 
            states.
        '''
        account_address = int(account_address)

        #Search one state in which the account_address exists
        world=None
        for state_id in self.all_state_ids:
            world = self.get_world(state_id)
            if account_address in world.storage:
                break


        with self.locked_context('coverage') as coverage:
            seen = coverage
        #runtime_bytecode = world.storage[account_address]['code']
        runtime_bytecode = self.get_metadata(account_address).runtime_bytecode


        end = None
        if  ''.join(runtime_bytecode[-44: -34]) =='\x00\xa1\x65\x62\x7a\x7a\x72\x30\x58\x20' \
            and  ''.join(runtime_bytecode[-2:]) =='\x00\x29':
            end = -9-33-2  #Size of metadata at the end of most contracts

        count, total = 0, 0
        for i in evm.EVMAsm.disassemble_all(runtime_bytecode[:end]) :
            if (account_address, i.offset) in seen:
                count += 1            
            total += 1

        return count*100.0/total

    def report_coverage(self, account_address):
        ''' Output a code coverage report for contract account_address '''
        account_address = int(account_address)
        #This will just pick one of the running states.
        #This assumes the code and the accounts are the same in all versions of the world
        #Search one state in which the account_address exists
        world=None
        for state_id in self.all_state_ids:
            world = self.get_world(state_id)
            if account_address in world.storage:
                break

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
        for i in evm.EVMAsm.disassemble_all(runtime_bytecode[:end]) :
            
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
