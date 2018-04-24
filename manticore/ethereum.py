from __future__ import division
from future import standard_library
standard_library.install_aliases()
from builtins import *
import string

from . import Manticore
from .manticore import ManticoreError
from .core.smtlib import ConstraintSet, Operators, issymbolic, Constant, operators
from .core.smtlib.visitors import arithmetic_simplifier
from .core.state import State, TerminateState
from .platforms import evm
from .utils.helpers import hex_encode

import tempfile
from subprocess import Popen, PIPE
from multiprocessing import Process, Queue
from queue import Empty as EmptyQueue
import sha3
import json
import logging
import io
import pickle
from .core.plugin import Plugin
from functools import reduce
from .utils.helpers import isunicode, isint, isstring

import binascii

logger = logging.getLogger(__name__)


################ Detectors ####################
class EthereumError(ManticoreError):
   pass


class NoAliveStates(EthereumError):
   pass


class Detector(Plugin):
    @property
    def name(self):
        return self.__class__.__name__.split('.')[-1]

    def get_findings(self, state):
        return state.context.setdefault('seth.findings.{!s}'.format(self.name), set())

    def add_finding(self, state, finding):
        address = state.platform.current.address
        pc = state.platform.current.pc
        self.get_findings(state).add((address, pc, finding))

        with self.manticore.locked_context('seth.global_findings', set) as global_findings:
            global_findings.add((address, pc, finding))
        logger.warning(finding)

    def _get_src(self, address, pc):
        return self.manticore.get_metadata(address).get_source_for(pc)

    def report(self, state):
        output = ''
        for address, pc, finding in self.get_findings(state):
            output += 'Finding {!s}\n'.format(finding)
            output += '\t Contract: {!s}\n'.format(address)
            output += '\t Program counter: {!s}\n'.format(pc)
            output += '\t Snippet:\n'
            output += '\n'.join(('\t\t' + x for x in self._get_src(address, pc).split('\n')))
            output += '\n'
        return output


class IntegerOverflow(Detector):
    '''
        Detects potential overflow and underflow conditions on ADD and SUB instructions.
    '''

    @staticmethod
    def _can_add_overflow(state, result, a, b):
        # TODO FIXME (mark) this is using a signed LT. need to check if this is correct
        return state.can_be_true(result < a) or state.can_be_true(result < b)

    @staticmethod
    def _can_mul_overflow(state, result, a, b):
        return state.can_be_true(operators.ULT(result, a) & operators.ULT(result, b))

    @staticmethod
    def _can_sub_underflow(state, a, b):
        return state.can_be_true(b > a)

    def did_evm_execute_instruction_callback(self, state, instruction, arguments, result):
        mnemonic = instruction.semantics

        if mnemonic == 'ADD':
            if self._can_add_overflow(state, result, *arguments):
                self.add_finding(state, "Integer overflow at {} instruction".format(mnemonic))
        elif mnemonic == 'MUL':
            if self._can_mul_overflow(state, result, *arguments):
                self.add_finding(state, "Integer overflow at {} instruction".format(mnemonic))
        elif mnemonic == 'SUB':
            if self._can_sub_underflow(state, *arguments):
                self.add_finding(state, "Integer underflow at {} instruction".format(mnemonic))


class UninitializedMemory(Detector):
    '''
        Detects uses of uninitialized memory
    '''

    def did_evm_read_memory_callback(self, state, offset, value):
        if not state.can_be_true(value != 0):
            # Not initialized memory should be zero
            return
        # check if offset is known
        cbu = True  # Can be unknown
        for known_address in state.context['seth.detectors.initialized_memory']:
            cbu = Operators.AND(cbu, offset != known_address)

        if state.can_be_true(cbu):
            self.add_finding(state, "Potentially reading uninitialized memory at instruction")

    def did_evm_write_memory_callback(self, state, offset, value):
        # concrete or symbolic write
        state.context.setdefault('seth.detectors.initialized_memory', set()).add(offset)


class UninitializedStorage(Detector):
    '''
        Detects uses of uninitialized storage
    '''

    def did_evm_read_storage_callback(self, state, offset, value):
        if not state.can_be_true(value != 0):
            # Not initialized memory should be zero
            return
        # check if offset is known
        cbu = True  # Can be unknown
        for known_address in state.context['seth.detectors.initialized_storage']:
            cbu = Operators.AND(cbu, offset != known_address)

        if state.can_be_true(cbu):
            self.add_finding(state, "Potentially reading uninitialized storage")

    def did_evm_write_storage_callback(self, state, offset, value):
        # concrete or symbolic write
        state.context.setdefault('seth.detectors.initialized_storage', set()).add(offset)


def remove_metadata(code):
    """
    Return provided bytecode without the metadata

    :param bytes code: bytecode
    :rtype bytes:
    """
    end = None
    if code[-44:-34] == bytes(b'\x00\xa1\x65\x62\x7a\x7a\x72\x30\x58\x20') and code[-2:] == bytes(b'\x00\x29'):
        end = -9 - 33 - 2
    return code[:end]


def calculate_coverage(code, seen):
    ''' Calculates what percentage of code has been seen '''
    runtime_bytecode = remove_metadata(code)

    count, total = 0, 0
    for i in evm.EVMAsm.disassemble_all(runtime_bytecode):
        if i.offset in seen:
            count += 1
        total += 1

    return count * 100.0 / total


class SolidityMetadata(object):
    def __init__(self, name, source_code, init_bytecode, runtime_bytecode, srcmap, srcmap_runtime, hashes, abi, warnings):
        ''' Contract metadata for Solidity-based contracts

            :param bytes source_code:
        '''
        self.name = name
        self.source_code = source_code.decode()
        self._init_bytecode = init_bytecode
        self._runtime_bytecode = runtime_bytecode
        self.hashes = hashes
        self.abi = {item.get(u'name', '{fallback}'): item for item in abi}
        self.warnings = warnings
        self.srcmap_runtime = self.__build_source_map(self.runtime_bytecode, srcmap_runtime)
        self.srcmap = self.__build_source_map(self.init_bytecode, srcmap)

    def __build_source_map(self, bytecode, srcmap):
        # https://solidity.readthedocs.io/en/develop/miscellaneous.html#source-mappings
        new_srcmap = {}
        bytecode = remove_metadata(bytecode)

        asm_offset = 0
        asm_pos = 0
        md = dict(enumerate(srcmap[asm_pos].split(':')))
        s = int(md.get(0, 0))
        l = int(md.get(1, 0))
        f = int(md.get(2, 0))
        j = md.get(3, None)

        for i in evm.EVMAsm.disassemble_all(bytecode):
            if asm_pos in srcmap and len(srcmap[asm_pos]):
                md = srcmap[asm_pos]
                if len(md):
                    d = {}
                    for p, k in enumerate(md.split(':')):
                        if len(k):
                            d[p] = k

                    s = int(d.get(0, s))
                    l = int(d.get(1, l))
                    f = int(d.get(2, f))
                    j = d.get(3, j)

            new_srcmap[asm_offset] = (s, l, f, j)
            asm_pos += 1
            asm_offset += i.size

        return new_srcmap

    @property
    def runtime_bytecode(self):
        return remove_metadata(self._runtime_bytecode)

    @property
    def init_bytecode(self):
        return remove_metadata(self._init_bytecode)

    def get_source_for(self, asm_offset, runtime=True):
        ''' Solidity source code snippet related to `asm_pos` evm bytecode offset.
            If runtime is False, initialization bytecode source map is used
        '''
        if runtime:
            srcmap = self.srcmap_runtime
        else:
            srcmap = self.srcmap

        try:
            beg, size, _, _ = srcmap[asm_offset]
        except KeyError:
            return u''

        output = u''
        nl = self.source_code.count('\n')
        snippet = self.source_code[beg:beg + size]
        for l in snippet.split('\n'):
            output += u'    {!s}  {!s}\n'.format(nl, l)
            nl += 1
        return output

    @property
    def signatures(self):
        return {b: a for (a, b) in self.hashes.items()}

    def get_abi(self, hsh):
        func_name = self.get_func_name(hsh)
        return self.abi[func_name]

    def get_func_argument_types(self, hsh):
        abi = self.get_abi(hsh)
        return '(' + ','.join(x['type'] for x in abi['inputs']) + ')'

    def get_func_return_types(self, hsh):
        abi = self.get_abi(hsh)
        return '(' + ','.join(x['type'] for x in abi['outputs']) + ')'

    def get_func_name(self, hsh):
        signature = self.signatures.get(hsh, '{fallback}()')
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

    class SByte(object):
        ''' Unconstrained symbolic byte, not associated with any ConstraintSet '''

        def __init__(self, size=1):
            self.size = size

        def __mul__(self, reps):
            return Symbol(self.size * reps)

    SCHAR = SByte(1)
    SUINT = SByte(32)
    SValue = None

    @staticmethod
    def serialize(value):
        '''
        Translates a Python object to its EVM ABI serialization.
        '''
        if isstring(value) or isinstance(value, tuple):
            return ABI.serialize_string(value)
        if isinstance(value, list):
            return ABI.serialize_array(value)
        if isint(value):
            return ABI.serialize_uint(value)
        if isinstance(value, ABI.SByte):
            return ABI.serialize_uint(value.size) + (None,) * value.size + (('\x00',) * (32 - (value.size % 32)))
        if value is None:
            return (None,) * 32

    @staticmethod
    def serialize_uint(value, size=32):
        '''
        Translates a Python int into a 32 byte string, MSB first
        '''
        assert size >= 1
        bytes = []
        for position in range(size):
            bytes.append(Operators.EXTRACT(value, position * 8, 8))
        chars = [Operators.CHR(s) for s in bytes]
        return tuple(reversed(chars))

    @staticmethod
    def serialize_string(value):
        '''
        Translates a string or a tuple of chars its EVM ABI serialization
        '''
        if not isstring(value) or isinstance(value, tuple):
            raise ValueError('serialize_string expected string or tuple, received {}'.format(type(value).__name__))
        return ABI.serialize_uint(len(value)) + tuple(value) + tuple('\x00'  * (32 - len(value) % 32))

    @staticmethod
    def serialize_array(value):
        assert isinstance(value, list)
        serialized = [ABI.serialize_uint(len(value))]
        for item in value:
            # TODO check all values are the same type
            serialized.append(ABI.serialize(item))
        return reduce(lambda x, y: x + y, serialized)

    @staticmethod
    def make_function_id(method_name_and_signature):
        '''
        Makes a function hash id from a method signature
        '''
        s = sha3.keccak_256()
        s.update(method_name_and_signature.encode())
        return bytes.fromhex(s.hexdigest()[:8])

    @staticmethod
    def make_function_arguments(*args):
        ''' Serializes a sequence of arguments '''
        if len(args) == 0:
            return ()
        args = list(args)
        for i in range(len(args)):
            if isinstance(args[i], EVMAccount):
                args[i] = int(args[i])
        result = []
        dynamic_args = []
        dynamic_offset = 32 * len(args)
        for arg in args:
            if isstring(arg) or isinstance(arg, (list, tuple, ManticoreEVM.SByte)):
                result.append(ABI.serialize(dynamic_offset))
                serialized_arg = ABI.serialize(arg)
                dynamic_args.append(serialized_arg)
                assert len(serialized_arg) % 32 == 0
                dynamic_offset += len(serialized_arg)
            else:
                result.append(ABI.serialize(arg))

        for arg in dynamic_args:
            result.append(arg)

        return reduce(lambda x, y: x + y, result)

    @staticmethod
    def make_function_call(method_name, *args):
        function_id = ABI.make_function_id(method_name)

        def check_bitsize(value, size):
            if isinstance(value, BitVec):
                return value.size == size
            return (value & ~((1 << size) - 1)) == 0
        assert len(function_id) == 4
        result = [tuple(function_id)]
        result.append(ABI.make_function_arguments(*args))
        return reduce(lambda x, y: x + y, result)

    @staticmethod
    def _consume_type(ty, data, offset):
        ''' INTERNAL parses a value of type from data '''
        def get_uint(size, offset):
            def simplify(x):
                value = arithmetic_simplifier(x)
                if isinstance(value, Constant) and not value.taint:
                    return value.value
                else:
                    return value

            size = simplify(size)
            offset = simplify(offset)
            byte_size = size // 8
            padding = 32 - byte_size  # for 160
            value = arithmetic_simplifier(Operators.CONCAT(size, *map(Operators.ORD, data[offset + padding:offset + padding + byte_size])))
            return simplify(value)

        if ty == u'uint256':
            return get_uint(256, offset), offset + 32
        elif ty in (u'bool', u'uint8'):
            return get_uint(8, offset), offset + 32
        elif ty == u'address':
            return get_uint(160, offset), offset + 32
        elif ty == u'int256':
            value = get_uint(256, offset)
            mask = 2**(256 - 1)
            value = -(value & mask) + (value & ~mask)
            return value, offset + 32
        elif ty == u'':
            return None, offset
        elif ty in (u'bytes', u'string'):
            dyn_offset = 4 + get_uint(256, offset)
            size = get_uint(256, dyn_offset)
            return data[dyn_offset + 32:dyn_offset + 32 + size], offset + 4
        elif ty.startswith('bytes') and 0 <= int(ty[5:]) <= 32:
            size = int(ty[5:])
            return data[offset:offset + size], offset + 32
        else:
            raise NotImplementedError(ty)

    @staticmethod
    def parse(signature, data):
        ''' Deserialize function ID and arguments specified in `signature` from `data` '''

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
            :param seth: the controlling Manticore
            :param default_caller: the default caller address for any transaction

        '''
        self._default_caller = default_caller
        self._seth = seth
        self._address = address
        self._hashes = None
        self._init_hashes()

    def __int__(self):
        return self._address

    def __str__(self):
        return str(self._address)

    @property
    def address(self):
        return self._address

    def _null_func(self):
        pass

    def _init_hashes(self):
        # initializes self._hashes lazy
        if self._hashes is None and self._seth is not None:
            self._hashes = {}
            md = self._seth.get_metadata(self._address)
            if md is not None:
                for signature, func_id in md.hashes.items():
                    func_name = str(signature.split('(')[0])
                    self._hashes[func_name] = signature, func_id
            # It was successful, no need to re-run. _init_hashes disabled
            self._init_hashes = self._null_func

    def __getattribute__(self, name):
        ''' If this is a contract account of which we know the functions hashes,
            this will build the transaction for the function call.

            Example use::

                #call funtion `add` on contract_account with argument `1000`
                contract_account.add(1000)

        '''
        if not name.startswith('_'):
            self._init_hashes()
            if self._hashes is not None and name in self._hashes:
                def f(*args, **kwargs):
                    caller = kwargs.get('caller', None)
                    value = kwargs.get('value', 0)
                    tx_data = ABI.make_function_call(self._hashes[name][0], *args)
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

        return object.__getattribute__(self, name)


class ManticoreEVM(Manticore):
    ''' Manticore EVM manager

        Usage Ex::

            from manticore.ethereum import ManticoreEVM, ABI
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
    SByte = ABI.SByte
    SValue = ABI.SValue

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
    def compile(source_code, contract_name=None):
        ''' Get initialization bytecode from a Solidity source code '''
        name, source_code, bytecode, runtime, srcmap, srcmap_runtime, hashes, abi, warnings = ManticoreEVM._compile(source_code, contract_name)
        return bytecode

    @staticmethod
    def _compile(source_code, contract_name):
        """ Compile a Solidity contract, used internally

            :param source_code: a solidity source code
            :param contract_name: a string with the name of the contract to analyze
            :return: name, source_code, bytecode, srcmap, srcmap_runtime, hashes
        """

        if isunicode(source_code):
            source_code = source_code.encode()

        solc = "solc"
        with tempfile.NamedTemporaryFile() as temp:
            temp.write(source_code)
            temp.flush()
            p = Popen([solc, '--combined-json', 'abi,srcmap,srcmap-runtime,bin,hashes,bin-runtime', '--allow-paths', '.', temp.name], stdout=PIPE, stderr=PIPE)

            try:
                output = json.loads(p.stdout.read().decode())
            except ValueError:
                raise Exception('Solidity compilation error:\n\n{}'.format(p.stderr.read()))

            contracts = output.get('contracts', [])
            if len(contracts) != 1 and contract_name is None:
                raise Exception('Solidity file must contain exactly one contract or you must use contract parameter to specify which one.')

            name, contract = None, None
            if contract_name is None:
                name, contract = next(iter(contracts.items()))
            else:
                for n, c in contracts.items():
                    if n.split(":")[1] == contract_name:
                        name, contract = n, c
                        break

            assert name is not None
            name = name.split(':')[1]

            if contract['bin'] == '':
                raise Exception('Solidity failed to compile your contract.')

            bytecode = bytes.fromhex(contract['bin'])
            runtime = bytes.fromhex(contract['bin-runtime'])
            srcmap = contract['srcmap'].split(';')
            srcmap_runtime = contract['srcmap-runtime'].split(';')
            hashes = contract['hashes']
            abi = json.loads(contract['abi'])
            warnings = p.stderr.read()
            return name, source_code, bytecode, runtime, srcmap, srcmap_runtime, hashes, abi, warnings

    def __init__(self, procs=1, **kwargs):
        ''' A Manticore EVM manager
            :param int procs: number of workers to use in the exploration
        '''
        self.normal_accounts = set()
        self.contract_accounts = set()
        self._config_procs = procs
        # Make the constraint store
        constraints = ConstraintSet()
        # make the ethereum world state
        world = evm.EVMWorld(constraints)
        initial_state = State(constraints, world)
        initial_state.context['tx'] = []
        super(ManticoreEVM, self).__init__(initial_state, **kwargs)

        self.detectors = {}
        self.metadata = {}

        # The following should go to manticore.context so we can use multiprocessing
        self.context['seth'] = {}
        self.context['seth']['_pending_transaction'] = None
        self.context['seth']['_saved_states'] = []
        self.context['seth']['_final_states'] = []
        self.context['seth']['_completed_transactions'] = 0

        self._executor.subscribe('did_load_state', self._load_state_callback)
        self._executor.subscribe('will_terminate_state', self._terminate_state_callback)
        self._executor.subscribe('will_execute_instruction', self._will_execute_instruction_callback)
        self._executor.subscribe('did_read_code', self._did_evm_read_code)
        self._executor.subscribe('on_symbolic_sha3', self._symbolic_sha3)
        self._executor.subscribe('on_concrete_sha3', self._concrete_sha3)

    @property
    def world(self):
        ''' The world instance or None if there is more than one state '''
        return self.get_world(None)

    @property
    def completed_transactions(self):
        with self.locked_context('seth') as context:
            return context['_completed_transactions']

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
        ''' IDs of the all states

            Note: state with id -1 is already in memory and it is not backed on the storage
        '''
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

    def count_states(self):
        ''' Total states count '''
        return len(self.terminated_state_ids + self.running_state_ids)

    def count_running_states(self):
        ''' Running states count '''
        return len(self.running_state_ids)

    def count_terminated_states(self):
        ''' Terminated states count '''
        return len(self.terminated_state_ids)

    def terminate_state_id(self, state_id):
        ''' Manually  terminates a states by state_id.
            Moves the state from the running list into the terminated list and
            generates a testcase for it
        '''
        if state_id != -1:
            with self.locked_context('seth') as seth_context:
                lst = seth_context['_saved_states']
                lst.remove(state_id)
                seth_context['_saved_states'] = lst

        state = self.load(state_id)
        last_exc = state.context['last_exception']
        self._generate_testcase_callback(state, 'test', last_exc.message)

        if state_id == -1:
            state_id = self.save(state, final=True)
            self._initial_state = None
        else:
            with self.locked_context('seth') as seth_context:
                lst = seth_context['_final_states']
                lst.append(state_id)
                seth_context['_final_states'] = lst

    # deprecate this 5 in favor of for sta in seth.all_states: do stuff?
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

    def get_code(self, address, state_id=None):
        ''' Storage data for `offset` on account `address` on state `state_id` '''
        if isinstance(address, EVMAccount):
            address = int(address)
        return self.get_world(state_id).storage[address]['code']

    def last_return(self, state_id=None):
        ''' Last returned buffer for state `state_id` '''
        state = self.load(state_id)
        return state.platform.last_return

    def transactions(self, state_id=None):
        ''' Transactions list for state `state_id` '''
        state = self.load(state_id)
        return state.platform.transactions

    def solidity_create_contract(self, source_code, owner, contract_name=None, balance=0, address=None, args=()):
        ''' Creates a solidity contract

            :param str source_code: solidity source code
            :param owner: owner account (will be default caller in any transactions)
            :type owner: int or EVMAccount
            :param contract_name: Name of the contract to analyze (optional if there is a single one in the source code)
            :type contract_name: str
            :param balance: balance to be transferred on creation
            :type balance: int or SValue
            :param address: the address for the new contract (optional)
            :type address: int or EVMAccount
            :param tuple args: constructor arguments
            :rtype: EVMAccount
        '''
        compile_results = self._compile(source_code, contract_name)
        init_bytecode = compile_results[2]

        if address is None:
            address = self.world.new_address()

        # FIXME different states "could"(VERY UNLIKELY) have different contracts
        # asociated with the same address
        self.metadata[address] = SolidityMetadata(*compile_results)

        account = self.create_contract(owner=owner,
                                       balance=balance,
                                       address=address,
                                       init=tuple(init_bytecode) + tuple(ABI.make_function_arguments(*args)))

        return account

    def create_contract(self, owner, balance=0, address=None, init=None):
        ''' Creates a contract

            :param owner: owner account (will be default caller in any transactions)
            :type owner: int or EVMAccount
            :param balance: balance to be transferred on creation
            :type balance: int or SValue
            :param int address: the address for the new contract (optional)
            :param str init: initializing evm bytecode and arguments
            :rtype: EVMAccount
        '''
        assert len(self.running_state_ids) == 1, "No forking yet"
        with self.locked_context('seth') as context:
            assert context['_pending_transaction'] is None
        assert init is not None
        if address is None:
            address = self.world.new_address()
        with self.locked_context('seth') as context:
            context['_pending_transaction'] = ('CREATE_CONTRACT', owner, address, balance, init)

        self.run(procs=self._config_procs)

        self.contract_accounts.add(address)

        return EVMAccount(address, self, default_caller=owner)

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
        address = self.world.create_account(address, balance, code=code, storage=None)
        self.normal_accounts.add(address)
        return address

    def transaction(self, caller, address, value, data):
        ''' Issue a symbolic transaction

            :param caller: the address of the account sending the transaction
            :type caller: int or EVMAccount
            :param address: the address of the contract to call
            :type address: int or EVMAccount
            :param value: balance to be transfered on creation
            :type value: int or SValue
            :param data: initial data
            :return: an EVMAccount
            :raises NoAliveStates: if there are no alive states to execute
        '''
        if isinstance(address, EVMAccount):
            address = int(address)
        if isinstance(caller, EVMAccount):
            caller = int(caller)

        with self.locked_context('seth') as context:
            has_alive_states = context['_saved_states'] or self.initial_state is not None
            if not has_alive_states:
                raise NoAliveStates

        if isinstance(data, self.SByte):
            data = (None,) * data.size
        with self.locked_context('seth') as context:
            context['_pending_transaction'] = ('CALL', caller, address, value, data)

        logger.info("Starting symbolic transaction: %d", self.completed_transactions + 1)

        status = self.run(procs=self._config_procs)

        with self.locked_context('seth') as context:
            context['_completed_transactions'] = context['_completed_transactions'] + 1

        logger.info("Finished symbolic transaction: %d | Code Coverage: %d%% | Terminated States: %d | Alive States: %d",
                    self.completed_transactions, self.global_coverage(address), len(self.terminated_state_ids), len(self.running_state_ids))

        return status

    def multi_tx_analysis(self, solidity_filename, contract_name=None, tx_limit=None, tx_account="attacker"):
        with open(solidity_filename) as f:
            source_code = f.read()

        owner_account = self.create_account(balance=1000)
        contract_account = self.solidity_create_contract(source_code, contract_name=contract_name, owner=owner_account)
        attacker_account = self.create_account(balance=1000)

        if tx_account == "attacker":
            tx_account = attacker_account
        elif tx_account == "owner":
            tx_account = owner_account
        else:
            raise EthereumError('The account to perform the symbolic exploration of the contract should be either "attacker" or "owner"')

        def run_symbolic_tx():
            symbolic_data = self.make_symbolic_buffer(320)
            symbolic_value = self.make_symbolic_value()
            self.transaction(caller=tx_account,
                             address=contract_account,
                             data=symbolic_data,
                             value=symbolic_value)

        prev_coverage = 0
        current_coverage = 0

        while current_coverage < 100:
            try:
                run_symbolic_tx()
            except NoAliveStates:
                break

            if tx_limit is not None:
                tx_limit -= 1
                if tx_limit == 0:
                    break

            prev_coverage = current_coverage
            current_coverage = self.global_coverage(contract_account)
            found_new_coverage = prev_coverage < current_coverage

            if not found_new_coverage:
                break

        self.finalize()

    def run(self, **kwargs):
        ''' Run any pending transaction on any running state '''

        # Check if there is a pending transaction
        with self.locked_context('seth') as context:
            assert context['_pending_transaction'] is not None

            # there is no states added to the executor queue
            assert len(self._executor.list()) == 0

            for state_id in context['_saved_states']:
                self._executor.put(state_id)
            context['_saved_states'] = []

        # A callback will use _pending_transaction and issue the transaction
        # in each state (see load_state_callback)
        super(ManticoreEVM, self).run(**kwargs)

        with self.locked_context('seth') as context:
            if len(context['_saved_states']) == 1:
                self._initial_state = self._executor._workspace.load_state(context['_saved_states'][0], delete=True)
                context['_saved_states'] = []
                assert self.running_state_ids == [-1]

            # clear pending transcations. We are done.
            context['_pending_transaction'] = None

    def save(self, state, final=False):
        ''' Save a state in secondary storage and add it to running or final lists

            :param state: A manticore State
            :param final: True if state is final
            :returns: a state id

        '''
        # save the state to secondary storage
        state_id = self._executor._workspace.save_state(state)

        with self.locked_context('seth') as context:
            if final:
                # Keep it on a private list
                context['_final_states'].append(state_id)
            else:
                # Keep it on a private list
                context['_saved_states'].append(state_id)
        return state_id

    def load(self, state_id=None):
        ''' Load one of the running or final states.

            :param state_id: If None it assumes there is a single running state
            :type state_id: int or None
        '''
        state = None
        if state_id is None:
            # a single state was assumed
            if len(self.running_state_ids) == 1:
                # Get the ID of the single running state
                state_id = self.running_state_ids[0]
            else:
                raise Exception("More than one state running.")

        if state_id == -1:
            state = self.initial_state
        else:
            state = self._executor._workspace.load_state(state_id, delete=False)
        return state

    # Callbacks
    def _symbolic_sha3(self, state, data, known_hashes):
        ''' INTERNAL USE '''

        with self.locked_context('known_sha3', set) as known_sha3:
            state.platform._sha3.update(known_sha3)

    def _concrete_sha3(self, state, buf, value):
        ''' INTERNAL USE '''
        with self.locked_context('known_sha3', set) as known_sha3:
            known_sha3.add((buf, value))

    def _terminate_state_callback(self, state, state_id, e):
        ''' INTERNAL USE
            Every time a state finishes executing last transaction we save it in
            our private list
        '''
        state.context['last_exception'] = e
        # TODO(mark): This will break if we ever change the message text. Use a less
        # brittle check.
        if isinstance(e, TerminateState) and e.message not in {'REVERT', 'THROW', 'TXERROR'}:
            # if not a revert we save the state for further transactioning
            state.context['processed'] = False
            if e.message == 'RETURN':
                with self.locked_context('seth') as context:
                    ty, caller, address, value, data = context['_pending_transaction']
                    if ty == 'CREATE_CONTRACT':
                        world = state.platform
                        world.storage[address]['code'] = world.last_return_data

            self.save(state)
            e.testcase = False  # Do not generate a testcase file
        else:
            self.save(state, final=True)

    # Callbacks
    def _load_state_callback(self, state, state_id):
        ''' INTERNAL USE
            When a state was just loaded from stoage we do the pending transaction
        '''
        if state.context.get('processed', False):
            return
        world = state.platform
        state.context['processed'] = True
        with self.locked_context('seth') as context:
            # take current global transaction we need to apply to all running states
            ty, caller, address, value, data = context['_pending_transaction']
            txnum = len(state.context['tx'])

        # Replace any none by symbolic values
        if value is None:
            value = state.new_symbolic_value(256, label='tx{:d}_value'.format(txnum))
        if isinstance(data, tuple):
            if any(x is None for x in data):
                symbolic_data = state.new_symbolic_buffer(label='tx{:d}_data'.format(txnum), nbytes=len(data))
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
        logger.debug("%s", state.platform.current)

        if isinstance(state.platform.current.last_exception, evm.Create):
            coverage_context_name = 'init_coverage'
            trace_context_name = 'seth.init.trace'
        else:
            coverage_context_name = 'runtime_coverage'
            trace_context_name = 'seth.rt.trace'

        with self.locked_context(coverage_context_name, set) as coverage:
            coverage.add((state.platform.current.address, state.platform.current.pc))

        state.context.setdefault(trace_context_name, []).append((state.platform.current.address, pc))

    def _did_evm_read_code(self, state, offset, size):
        ''' INTERNAL USE '''
        with self.locked_context('code_data', set) as code_data:
            for i in range(offset, offset + size):
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

    def generate_testcase(self, state, name, message=''):
        self._generate_testcase_callback(state, name, message)
    
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
        # TODO(mark): Refactor ManticoreOutput to let the platform be more in control
        #  so this function can be fully ported to EVMWorld.generate_workspace_files.

        def flagged(flag):
            return '(*)' if flag else ''

        testcase = self._output.testcase(name)
        logger.info("Generated testcase No. {} - {}".format(testcase.num, message))
        blockchain = state.platform
        with testcase.open_stream('summary') as summary:
            summary.write(u"Last exception: {!s}\n".format(state.context['last_exception']))

            address, offset = state.context['seth.rt.trace'][-1]

            # Last instruction
            metadata = self.get_metadata(blockchain.transactions[-1].address)
            if metadata is not None:
                summary.write(u'Last instruction at contract {:x} offset {:x}\n'.format(address, offset))
                at_runtime = blockchain.transactions[-1].sort != 'Create'
                summary.write(metadata.get_source_for(offset, at_runtime))
                summary.write(u'\n')

            # Accounts summary
            is_something_symbolic = False
            summary.write(u"{:d} accounts.\n".format(len(blockchain.accounts)))
            for account_address in blockchain.accounts:
                summary.write(u"Address: 0x{:x}\n".format(account_address))
                balance = blockchain.get_balance(account_address)
                is_balance_symbolic = issymbolic(balance)
                is_something_symbolic = is_something_symbolic or is_balance_symbolic
                balance = state.solve_one(balance)
                summary.write(u"Balance: {:d} {!s}\n".format(balance, flagged(is_balance_symbolic)))

                if blockchain.has_storage(account_address):
                    summary.write(u"Storage:\n")
                    for offset, value in blockchain.get_storage_items(account_address):
                        is_storage_symbolic = issymbolic(offset) or issymbolic(value)
                        offset = state.solve_one(offset)
                        value = state.solve_one(value)
                        summary.write(u"\t{:032x} -> {:032x} {!s}\n".format(offset, value, flagged(is_storage_symbolic)))
                        is_something_symbolic = is_something_symbolic or is_storage_symbolic

                runtime_code = blockchain.get_code(account_address)
                if runtime_code:
                    summary.write(u"Code:\n")
                    fcode = io.BytesIO(runtime_code)
                    for chunk in iter(lambda: fcode.read(32), b''):
                        summary.write(u'\t{}\n'.format(binascii.hexlify(chunk)))
                    runtime_trace = set((pc for contract, pc in state.context['seth.rt.trace'] if address == contract))
                    summary.write(u"Coverage {:0.3f}% (on this state)\n".format(calculate_coverage(runtime_code, runtime_trace)))  # coverage % for address in this account/state
                summary.write(u"\n")

            if blockchain._sha3:
                summary.write(u"Known hashes:\n")
                for key, value in blockchain._sha3.items():
                    summary.write(u'{!s}::{:x}\n'.format(hex_encode(key), value))

            if is_something_symbolic:
                summary.write(u'\n\n(*) Example solution given. Value is symbolic and may take other values\n')

        # Transactions
        with testcase.open_stream('tx') as tx_summary:
            is_something_symbolic = False
            for tx in blockchain.transactions:  # external transactions
                tx_summary.write(u"Transactions Nr. {:d}\n".format(blockchain.transactions.index(tx)))

                # The result if any RETURN or REVERT
                tx_summary.write(u"Type: {!s}\n".format(tx.sort))
                tx_summary.write(u"From: 0x{:x}\n".format(state.solve_one(tx.caller), flagged(issymbolic(tx.caller))))
                tx_summary.write(u"To: 0x{:x} {!s}\n".format(state.solve_one(tx.address), flagged(issymbolic(tx.address))))
                tx_summary.write(u"Value: {:d} {!s}\n".format(state.solve_one(tx.value), flagged(issymbolic(tx.value))))
                tx_summary.write(u"Data: {!s} {!s}\n".format(hex_encode(state.solve_one(tx.data)), flagged(issymbolic(tx.data))))


                if tx.return_data is not None:
                    return_data = state.solve_one(tx.return_data)
                    tx_summary.write(u"Return_data: {!s} {!s}\n".format(hex_encode(return_data), flagged(issymbolic(tx.return_data))))

                metadata = self.get_metadata(tx.address)
                if tx.sort == 'Call':
                    if metadata is not None:
                        function_id = tx.data[:4]  #hope there is enough data
                        function_id = hex_encode(state.solve_one(function_id))
                        signature = metadata.get_func_signature(function_id)
                        function_name, arguments = ABI.parse(signature, tx.data)
                        if tx.result == 'RETURN':
                            ret_types = metadata.get_func_return_types(function_id)
                            return_data = ABI.parse(ret_types, tx.return_data)  # function return

                        tx_summary.write(u'\n')
                        tx_summary.write(u"Function call:\n")
                        tx_summary.write(u"{!s}(".format(state.solve_one(function_name)))
                        tx_summary.write(u','.join(map(repr, map(state.solve_one, arguments))))
                        is_argument_symbolic = any(map(issymbolic, arguments))
                        is_something_symbolic = is_something_symbolic or is_argument_symbolic
                        tx_summary.write(u') -> {!s} {!s}\n'.format(tx.result, flagged(is_argument_symbolic)))

                        if return_data is not None:
                            is_return_symbolic = any(map(issymbolic, return_data))
                            return_values = tuple(map(state.solve_one, return_data))
                            if len(return_values) == 1:
                                return_values = return_values[0]

                            tx_summary.write(u'return: {!r} {!s}\n'.format(return_values, flagged(is_return_symbolic)))
                            is_something_symbolic = is_something_symbolic or is_return_symbolic

                tx_summary.write(u'\n\n')

            if is_something_symbolic:
                tx_summary.write(u'\n\n(*) Example solution given. Value is symbolic and may take other values\n')

        # logs
        with testcase.open_stream('logs') as logs_summary:
            is_something_symbolic = False
            for log_item in blockchain.logs:
                is_log_symbolic = issymbolic(log_item.memlog)
                is_something_symbolic = is_log_symbolic or is_something_symbolic
                solved_memlog = state.solve_one(log_item.memlog)
                printable_bytes = bytes([c for c in solved_memlog if chr(c) in string.printable])

                logs_summary.write(u"Address: {:x}\n".format(log_item.address))
                logs_summary.write(u"Memlog: {!s} ({!s}) {!s}\n".format(binascii.hexlify(solved_memlog), printable_bytes, flagged(is_log_symbolic)))
                logs_summary.write(u"Topics:\n")
                for i, topic in enumerate(log_item.topics):
                    logs_summary.write(u"\t{:d}) {:x} {!s}".format(i, state.solve_one(topic), flagged(issymbolic(topic))))

        with testcase.open_stream('constraints') as smt_summary:
            smt_summary.write(str(state.constraints))

        with testcase.open_stream('pkl', binary=True) as statef:
            try:
                statef.write(pickle.dumps(state, 2))
            except RuntimeError:
                # recursion exceeded. try a slower, iterative solution
                from .utils import iterpickle
                logger.debug("Using iterpickle to dump state")
                statef.write(iterpickle.dumps(state, 2))

        with testcase.open_stream('rt.trace') as f:
            self._emit_trace_file(f, state.context['seth.rt.trace'])

        with testcase.open_stream('init.trace') as f:
            self._emit_trace_file(f, state.context['seth.init.trace'])

    @staticmethod
    def _emit_trace_file(filestream, trace):
        """
        :param filestream: file object for the workspace trace file. should be opened in non-binary mode
        :param trace: list of (contract address, pc) tuples
        :type trace: list[tuple(int, int)]
        """

        for contract, pc in trace:
            if pc == 0:
                filestream.write(u'---\n')
            ln = u'0x{:x}:0x{:x}\n'.format(contract, pc)
            filestream.write(ln)

    def finalize(self):
        """
        Terminate and generate testcases for all currently alive states (contract states that cleanly executed
        to a STOP or RETURN in the last symbolic transaction).
        """

        # move runnign states to final states list
        # and generate a testcase for each
        q = Queue()
        for running_state_id in self.running_state_ids:
            q.put(running_state_id)

        def f(q):
            try:
                while True:
                    state_id = q.get_nowait()
                    self.terminate_state_id(state_id)
            except EmptyQueue:
                pass

        ps = []

        for _ in range(self._config_procs):
            p = Process(target=f, args=(q,))
            p.start()
            ps.append(p)

        for p in ps:
            p.join()

        # delete actual streams from storage
        for state_id in self.all_state_ids:
            # state_id -1 is always only on memory
            if state_id != -1:
                self._executor._workspace.rm_state(state_id)

        # clean up lists
        with self.locked_context('seth') as seth_context:
            seth_context['_saved_states'] = []
        with self.locked_context('seth') as seth_context:
            seth_context['_final_states'] = []

        #global summary
        with self._output.save_stream('global.summary') as global_summary:
            # (accounts created by contract code are not in this list )
            global_summary.write(u"Global coverage:\n")
            for address in self.contract_accounts:
                global_summary.write(u"{:x}: {:0.3f}%\n".format(address, self.global_coverage(address)))  # coverage % for address in this state

            if len(self.global_findings):
                global_summary.write(u"Global Findings:\n")

                for address, pc, finding in self.global_findings:
                    global_summary.write(u'- {!s} -\n'.format(finding))
                    global_summary.write(u'\t Contract: {!s}\n'.format(address))
                    global_summary.write(u'\t Program counter: {!s}\n'.format(pc))
                    md = self.get_metadata(address)
                    if md is not None:
                        src = md.get_source_for(pc)
                        global_summary.write(u'\t Snippet:\n')
                        global_summary.write(u'\n'.join(('\t\t' + x for x in src.split('\n'))))
                        global_summary.write(u'\n\n')

            md = self.get_metadata(address)
            if md is not None and len(md.warnings) > 0:
                global_summary.write(u'\n\nCompiler warnings for {!s}:\n'.format(md.name))
                global_summary.write(md.warnings.decode())

        for address, md in self.metadata.items():
            with self._output.save_stream('global_{!s}.sol'.format(md.name)) as global_src:
                global_src.write(md.source_code)
            with self._output.save_stream('global_{!s}_runtime.bytecode'.format(md.name), binary=True) as global_runtime_bytecode:
                global_runtime_bytecode.write(md.runtime_bytecode)
            with self._output.save_stream('global_{!s}_init.bytecode'.format(md.name), binary=True) as global_init_bytecode:
                global_init_bytecode.write(md.init_bytecode)

            with self._output.save_stream('global_{!s}.runtime_asm'.format(md.name)) as global_runtime_asm:
                runtime_bytecode = md.runtime_bytecode

                with self.locked_context('runtime_coverage') as seen:

                    count, total = 0, 0
                    for i in evm.EVMAsm.disassemble_all(runtime_bytecode):
                        if (address, i.offset) in seen:
                            count += 1
                            global_runtime_asm.write(u'*')
                        else:
                            global_runtime_asm.write(u' ')

                        global_runtime_asm.write(u'{:4x}: {!s}\n'.format(i.offset, i))
                        total += 1

            with self._output.save_stream('global_{!s}.init_asm'.format(md.name)) as global_init_asm:
                with self.locked_context('init_coverage') as seen:
                    count, total = 0, 0
                    for i in evm.EVMAsm.disassemble_all(md.init_bytecode):
                        if (address, i.offset) in seen:
                            count += 1
                            global_init_asm.write(u'*')
                        else:
                            global_init_asm.write(u' ')

                        global_init_asm.write(u'{:4x}: {!s}\n'.format(i.offset, i))
                        total += 1

            with self._output.save_stream('global_{!s}.init_visited'.format(md.name)) as f:
                with self.locked_context('init_coverage') as seen:
                    visited = set((o for (a, o) in seen if a == address))
                    for o in sorted(visited):
                        f.write(u'0x{:x}\n'.format(o))

            with self._output.save_stream('global_{!s}.runtime_visited'.format(md.name)) as f:
                with self.locked_context('runtime_coverage') as seen:
                    visited = set()
                    for (a, o) in seen:
                        if a == address:
                            visited.add(o)
                    for o in sorted(visited):
                        f.write(u'0x{:x}\n'.format(o))

        logger.info(u"Results in %s", self.workspace)

    def global_coverage(self, account_address):
        ''' Returns code coverage for the contract on `account_address`.
            This sums up all the visited code lines from any of the explored
            states.
        '''
        account_address = int(account_address)

        # Search one state in which the account_address exists
        world = None
        for state_id in self.all_state_ids:
            world = self.get_world(state_id)
            if account_address in world.storage:
                break

        with self.locked_context('runtime_coverage') as coverage:
            seen = coverage
        #runtime_bytecode = world.storage[account_address]['code']
        runtime_bytecode = self.get_metadata(account_address).runtime_bytecode

        count, total = 0, 0
        for i in evm.EVMAsm.disassemble_all(runtime_bytecode):
            if (account_address, i.offset) in seen:
                count += 1
            total += 1

        return count * 100.0 / total

    # TODO: Find a better way to suppress execution of Manticore._did_finish_run_callback
    # We suppress because otherwise we log it many times and it looks weird.
    def _did_finish_run_callback(self):
        pass
