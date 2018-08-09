''' Symbolic EVM implementation based on the yellow paper: http://gavwood.com/paper.pdf '''
import random
import copy
import inspect
from functools import wraps
from ..utils.helpers import issymbolic, memoized, get_taints, taint_with, istainted
from ..platforms.platform import *
from ..core.smtlib import solver, BitVec, Array, Operators, Constant, ArrayVariable, BitVecConstant, translate_to_smtlib
from ..core.state import Concretize, TerminateState
from ..core.plugin import Ref
from ..utils.event import Eventful
from ..core.smtlib.visitors import simplify
import pyevmasm as EVMAsm
import logging
from collections import namedtuple
import sha3

logger = logging.getLogger(__name__)

#fixme make it gobal using this https://docs.python.org/3/library/configparser.html
#and save it at the workspace so results are reproducible
config = namedtuple("config", "out_of_gas")
config.out_of_gas = None  # 0: default not enough gas, 1 default to always enough gas, 2: for on both

# Auxiliar constants and functions
TT256 = 2 ** 256
TT256M1 = 2 ** 256 - 1
MASK160 = 2 ** 160 - 1
TT255 = 2 ** 255
TOOHIGHMEM = 0x1000

#FIXME. We should just use a Transaction() for this
PendingTransaction = namedtuple("PendingTransaction", ['type', 'address', 'price', 'data', 'caller', 'value', 'gas'])
EVMLog = namedtuple("EVMLog", ['address', 'memlog', 'topics'])


def ceil32(x):
    size = 256
    if isinstance(x, BitVec):
        size = x.size
    return Operators.ITEBV(size, Operators.UREM(x, 32) == 0, x, x + 32 - Operators.UREM(x, 32))


def to_signed(i):
    return Operators.ITEBV(256, i < TT255, i, i - TT256)


class Transaction(object):
    __slots__ = '_sort', 'address', 'price', 'data', 'caller', 'value', 'depth', '_return_data', '_result', 'gas'

    def __init__(self, sort, address, price, data, caller, value, gas=0, depth=None, result=None, return_data=None):
        self.sort = sort
        self.address = address
        self.price = price
        self.data = data
        self.caller = caller
        self.value = value
        self.depth = depth
        self.gas = gas
        self.set_result(result, return_data)

    @property
    def sort(self):
        return self._sort

    @sort.setter
    def sort(self, sort):
        if sort not in {'CREATE', 'CALL', 'DELEGATECALL'}:
            raise EVMException('Invalid transaction type')
        self._sort = sort

    @property
    def result(self):
        return self._result

    def is_human(self):
        return self.depth == 0

    @property
    def return_data(self):
        return self._return_data

    @property
    def return_value(self):
        if self.result in {'RETURN', 'STOP'}:
            return 1
        else:
            assert self.result in {'TXERROR', 'REVERT', 'THROW', 'SELFDESTRUCT'}
            return 0

    def set_result(self, result, return_data=None):
        if getattr(self, 'result', None) is not None:
            raise EVMException('Transaction result already set')
        if result not in {None, 'TXERROR', 'REVERT', 'RETURN', 'THROW', 'STOP', 'SELFDESTRUCT'}:
            raise EVMException('Invalid transaction result')
        if result in {'RETURN', 'REVERT'}:
            if not isinstance(return_data, (bytearray, Array)):
                raise EVMException('Invalid transaction return_data')
        else:
            if return_data is not None:
                raise EVMException('Invalid transaction return_data')
        self._result = result
        self._return_data = return_data

    def __reduce__(self):
        ''' Implements serialization/pickle '''
        return (self.__class__, (self.sort, self.address, self.price, self.data, self.caller, self.value, self.gas, self.depth, self.result, self.return_data))

    def __str__(self):
        return 'Transaction({:s}, from=0x{:x}, to=0x{:x}, value={!r}, depth={:d}, data={!r}, result={!r}..)'.format(self.sort, self.caller, self.address, self.value, self.depth, self.data, self.result)


# Exceptions...

class EVMException(Exception):
    pass


class Emulated(EVMException):
    def __init__(self, result):
        super().__init__("Emulated instruction")
        self.result = result


class ConcretizeStack(EVMException):
    '''
    Raised when a symbolic memory cell needs to be concretized.
    '''

    def __init__(self, pos, expression=None, policy='MINMAX'):
        self.message = "Concretizing evm stack item {}".format(pos)
        self.pos = pos
        self.expression = expression
        self.policy = policy


class Sha3(EVMException):
    def __init__(self, data):
        self.data = data

    def __reduce__(self):
        return (self.__class__, (self.data, ))


class StartTx(EVMException):
    ''' A new transaction is started '''
    pass


class EndTx(EVMException):
    ''' The current transaction ends'''

    def __init__(self, result, data=None):
        if result not in {None, 'TXERROR', 'REVERT', 'RETURN', 'THROW', 'STOP', 'SELFDESTRUCT'}:
            raise EVMException('Invalid end transaction result')
        if result is None and data is not None:
            raise EVMException('Invalid end transaction result')
        if not isinstance(data, (type(None), Array, bytearray)):
            raise EVMException('Invalid end transaction data type')

        self.result = result
        self.data = data

    def is_rollback(self):
        if self.result in {'STOP', 'RETURN', 'SELFDESTRUCT'}:
            return False
        else:
            assert self.result in {'THROW', 'TXERROR', 'REVERT'}
            return True


class StackOverflow(EndTx):
    ''' Attemped to push more than 1024 items '''

    def __init__(self):
        super().__init__('THROW')


class StackUnderflow(EndTx):
    ''' Attemped to popo from an empty stack '''

    def __init__(self):
        super().__init__('THROW')


class InvalidOpcode(EndTx):
    ''' Trying to execute invalid opcode '''

    def __init__(self):
        super().__init__('THROW')


class NotEnoughGas(EndTx):
    ''' Not enough gas for operation '''

    def __init__(self):
        super().__init__('THROW')


class Stop(EndTx):
    ''' Program reached a STOP instruction '''

    def __init__(self):
        super().__init__('STOP')


class Return(EndTx):
    ''' Program reached a RETURN instruction '''

    def __init__(self, data=bytearray()):
        super().__init__('RETURN', data)


class Revert(EndTx):
    ''' Program reached a REVERT instruction '''

    def __init__(self, data):
        super().__init__('REVERT', data)


class SelfDestruct(EndTx):
    ''' Program reached a SELFDESTRUCT instruction '''

    def __init__(self):
        super().__init__('SELFDESTRUCT')


class TXError(EndTx):
    ''' A failed Transaction '''

    def __init__(self):
        super().__init__('TXERROR')


def concretized_args(**policies):
    """
    Make sure an EVM instruction has all of its arguments concretized according to
    provided policies.

    Example decoration:

        @concretized_args(size='ONE', address='')
        def LOG(self, address, size, *topics):
            ...

    The above will make sure that the |size| parameter to LOG is Concretized when symbolic
    according to the 'ONE' policy and concretize |address| with the default policy.

    :param policies: A kwargs list of argument names and their respective policies.
                         Provide None or '' as policy to use default.
    :return: A function decorator
    """
    def concretizer(func):
        @wraps(func)
        def wrapper(*args, **kwargs):
            spec = inspect.getfullargspec(func)
            for arg, policy in policies.items():
                assert arg in spec.args, "Concretizer argument not found in wrapped function."
                # index is 0-indexed, but ConcretizeStack is 1-indexed. However, this is correct
                # since implementation method is always a bound method (self is param 0)
                index = spec.args.index(arg)
                if not issymbolic(args[index]):
                    continue
                if not policy:
                    raise ConcretizeStack(index)
                if policy == "ACCOUNTS":
                    #special handler for EVM only policy
                    address = args[index]
                    world = args[0].world
                    cond = world._constraint_to_accounts(address, ty='both', include_zero=True)
                    world.constraints.add(cond)
                    policy = 'ALL'
                raise ConcretizeStack(index, policy=policy)
            return func(*args, **kwargs)
        return wrapper
    return concretizer


class EVM(Eventful):
    '''Machine State. The machine state is defined as
        the tuple (g, pc, m, i, s) which are the gas available, the
        program counter pc , the memory contents, the active
        number of words in memory (counting continuously
        from position 0), and the stack contents. The memory
        contents are a series of zeroes of bitsize 256
    '''
    _published_events = {'evm_execute_instruction',
                         'evm_read_storage', 'evm_write_storage',
                         'evm_read_memory',
                         'evm_write_memory',
                         'evm_read_code',
                         'decode_instruction', 'execute_instruction', 'concrete_sha3', 'symbolic_sha3'}

    class transact(object):
        "Emulate PyProperty_Type() in Objects/descrobject.c"

        def __init__(self, pre=None, pos=None, doc=None):
            self._pre = pre
            self._pos = pos
            if doc is None and pre is not None:
                doc = pre.__doc__
            self.__doc__ = doc
            self.__name__ = pre.__name__

        def __get__(self, obj, objtype=None):
            if obj is None:
                return self
            if self._pre is None:
                raise AttributeError("unreadable attribute")
            from types import MethodType

            #return different version depending on obj._pending_transaction
            def _pre_func(my_obj, *args, **kwargs):
                if my_obj._on_transaction:
                    my_obj._on_transaction = False
                    return self._pos(my_obj, *args, **kwargs)
                else:
                    my_obj._on_transaction = True
                    return self._pre(my_obj, *args, **kwargs)

            return MethodType(_pre_func, obj)

        def __set__(self, obj, value):
            raise AttributeError("can't set attribute")

        def __delete__(self, obj):
            raise AttributeError("can't delete attribute")

        def pos(self, pos):
            return type(self)(self._pre, pos)

    def __init__(self, constraints, address, data, caller, value, bytecode, world=None, gas=210000, **kwargs):
        '''
        Builds a Ethereum Virtual Machine instance

        :param memory: the initial memory
        :param address: the address of the account which owns the code that is executing.
        :param data: the byte array that is the input data to this execution
        :param caller: the address of the account which caused the code to be executing. A 160-bit code used for identifying Accounts
        :param value: the value, in Wei, passed to this account as part of the same procedure as execution. One Ether is defined as being 10**18 Wei
        :param bytecode: the byte array that is the machine code to be executed
        :param world: the EVMWorld object where the transaction is being executed
        :param gas: gas budget for this transaction

        '''
        super().__init__(**kwargs)
        if data is not None and not issymbolic(data):
            data_size = len(data)
            data_symbolic = constraints.new_array(index_bits=256, value_bits=8, index_max=data_size, name='DATA')
            data_symbolic[0:data_size] = data
            data = data_symbolic

        if bytecode is not None and not issymbolic(bytecode):
            bytecode_size = len(bytecode)
            bytecode_symbolic = constraints.new_array(index_bits=256, value_bits=8, index_max=bytecode_size, name='BYTECODE')
            bytecode_symbolic[0:bytecode_size] = bytecode
            bytecode = bytecode_symbolic

        #A no code VM is used to execute transactions to normal accounts.
        #I'll execute a STOP and close the transaction
        #if len(bytecode) == 0:
        #    raise EVMException("Need code")
        self._constraints = constraints
        self.memory = constraints.new_array(index_bits=256, value_bits=8, name='EMPTY_MEMORY')
        self.address = address
        self.caller = caller  # address of the account that is directly responsible for this execution
        self.data = data
        self.value = value
        self._bytecode = bytecode
        self.suicides = set()
        self.logs = []
        #FIXME parse decode and mark invalid instructions
        #self.invalid = set()

        # Machine state
        self.pc = 0
        self.stack = []
        self._gas = gas
        self._world = world
        self._allocated = 0
        self._on_transaction = False  # for @transact

    @property
    def bytecode(self):
        return self._bytecode

    @property
    def constraints(self):
        return self._constraints

    @constraints.setter
    def constraints(self, constraints):
        self._constraints = constraints
        self.memory.constraints = constraints

    @property
    def gas(self):
        return self._gas

    def __getstate__(self):
        state = super().__getstate__()
        state['memory'] = self.memory
        state['world'] = self._world
        state['constraints'] = self.constraints
        state['address'] = self.address
        state['caller'] = self.caller
        state['data'] = self.data
        state['value'] = self.value
        state['bytecode'] = self._bytecode
        state['pc'] = self.pc
        state['stack'] = self.stack
        state['gas'] = self._gas
        state['allocated'] = self._allocated
        state['suicides'] = self.suicides
        state['logs'] = self.logs
        state['_on_transaction'] = self._on_transaction
        return state

    def __setstate__(self, state):
        self._on_transaction = state['_on_transaction']
        self._gas = state['gas']
        self.memory = state['memory']
        self.logs = state['logs']
        self._world = state['world']
        self.constraints = state['constraints']
        self.address = state['address']
        self.caller = state['caller']
        self.data = state['data']
        self.value = state['value']
        self._bytecode = state['bytecode']
        self.pc = state['pc']
        self.stack = state['stack']
        self._allocated = state['allocated']
        self.suicides = state['suicides']
        super().__setstate__(state)

    def _allocate(self, address):
        allocated = self.allocated
        GMEMORY = 3
        GQUADRATICMEMDENOM = 512  # 1 gas per 512 quadwords
        old_size = Operators.ZEXTEND(Operators.UDIV(self.safe_add(allocated, 31), 32), 512)
        new_size = Operators.ZEXTEND(Operators.UDIV(self.safe_add(address, 31), 32), 512)

        old_totalfee = self.safe_mul(old_size, GMEMORY) + Operators.UDIV(self.safe_mul(old_size, old_size), GQUADRATICMEMDENOM)
        new_totalfee = self.safe_mul(new_size, GMEMORY) + Operators.UDIV(self.safe_mul(new_size, new_size), GQUADRATICMEMDENOM)
        memfee = new_totalfee - old_totalfee
        flag = Operators.UGT(new_totalfee, old_totalfee)
        self._consume(Operators.ITEBV(512, flag, memfee, 0))

        address_c = Operators.UDIV(self.safe_add(address, 31), 32) * 32
        self._allocated = Operators.ITEBV(512, flag, Operators.ZEXTEND(address_c, 512), Operators.ZEXTEND(allocated, 512))

    @property
    def allocated(self):
        return self._allocated

    @property
    def world(self):
        return self._world

    @staticmethod
    def check256int(value):
        assert True

    def read_code(self, address, size=1):
        '''
            Read size byte from bytecode.
            If less than size bytes are available result will be pad with \x00
        '''
        assert address < len(self.bytecode)
        value = self.bytecode[address:address + size]
        if len(value) < size:
            value += '\x00' * (size - len(value))  # pad with null (spec)
        return value

    def disassemble(self):
        return EVMAsm.disassemble(self.bytecode)

    @property
    def PC(self):
        return self.pc

    @property
    def instruction(self):
        '''
            Current instruction pointed by self.pc
        '''
        # FIXME check if pc points to invalid instruction
        # if self.pc >= len(self.bytecode):
        #    return InvalidOpcode('Code out of range')
        # if self.pc in self.invalid:
        #    raise InvalidOpcode('Opcode inside a PUSH immediate')
        try:
            _decoding_cache = getattr(self, '_decoding_cache')
        except:
            _decoding_cache = self._decoding_cache = {}

        pc = self.pc
        if isinstance(pc, Constant):
            pc = pc.value

        if pc in _decoding_cache:
            return _decoding_cache[pc]

        def getcode():
            bytecode = self.bytecode
            for pc_i in range(pc, len(bytecode)):
                yield simplify(bytecode[pc_i]).value
            while True:
                yield 0
        instruction = EVMAsm.disassemble_one(getcode(), pc=pc)
        _decoding_cache[pc] = instruction
        return instruction

    # auxiliar funcs
    # Stack related
    def _push(self, value):
        '''
                   ITEM0
                   ITEM1
                   ITEM2
             sp->  {empty}
        '''
        assert isinstance(value, int) or isinstance(value, BitVec) and value.size == 256
        if len(self.stack) >= 1024:
            raise StackOverflow()

        if isinstance(value, int):
            value = value & TT256M1

        value = simplify(value)
        if isinstance(value, Constant) and not value.taint:
            value = value.value
        self.stack.append(value)

    def _top(self, n=0):
        ''' Read a value from the top of the stack without removing it '''
        if len(self.stack) - n < 0:
            raise StackUnderflow()
        return self.stack[n - 1]

    def _pop(self):
        ''' Pop a value from the stack '''
        if len(self.stack) == 0:
            raise StackUnderflow()
        return self.stack.pop()

    def _consume(self, fee):
        if isinstance(fee, int):
            if fee > (1 << 512) - 1:
                raise ValueError
        elif isinstance(fee, BitVec):
            if (fee.size != 512):
                raise EthereumError("Fees should be 512 bit long")

        self.constraints.add(Operators.UGE(fee, 0))
        self.constraints.add(Operators.ULE(fee, self._gas))

        #FIXME add configurable checks here
        if config.out_of_gas is not None:
            if config.out_of_gas == 0:
                #default to OOG exception if possible
                if solver.can_be_true(self.constraints, self._gas < fee):
                    self.constraints.add(Operators.UGT(fee, self.gas))
                    logger.debug("Not enough gas for instruction")
                    raise NotEnoughGas()
            elif config.out_of_gas == 1:
                #default to enough gas if possible
                if solver.can_be_true(self.constraints, self._gas > fee):
                    self.constraints.add(Operators.UGT(self.gas, fee))
                else:
                    logger.debug("Not enough gas for instruction")
                    raise NotEnoughGas()
            else:
                #fork on both options
                if len(solver.get_all_values(self.constraints, self._gas > fee)) == 2:
                    raise Concretize("Concretice gas fee",
                                     expression=self._gas > fee,
                                     setstate=None,
                                     policy='ALL')

        self._gas -= fee

    def _indemnify(self, fee):
        self._gas += fee

    def _pop_arguments(self):
        #Get arguments (imm, pop)
        current = self.instruction
        arguments = []
        if self.instruction.has_operand:
            arguments.append(current.operand)
        for _ in range(current.pops):
            arguments.append(self._pop())
        # simplify stack arguments
        for i in range(len(arguments)):
            #if isinstance(arguments[i], Expression):
            #    arguments[i] = simplify(arguments[i])
            if isinstance(arguments[i], Constant) and not arguments[i].taint:
                arguments[i] = arguments[i].value
        return arguments

    def _push_arguments(self, arguments):
        #Immediate operands should not be pushed
        start = int(self.instruction.has_operand)
        for arg in reversed(arguments[start:]):
            self._push(arg)

    def _push_results(self, instruction, result):
        # Check result (push)
        if instruction.pushes > 1:
            assert len(result) == instruction.pushes
            for value in reversed(result):
                self._push(value)
        elif instruction.pushes == 1:
            self._push(result)
        else:
            assert instruction.pushes == 0
            assert result is None

    def _handler(self, *arguments):
        current = self.instruction
        implementation = getattr(self, current.semantics, None)
        if implementation is None:
            raise TerminateState("Instruction not implemented %s" % current.semantics, testcase=True)
        return implementation(*arguments)

    #Execute an instruction from current pc
    def execute(self):
        if issymbolic(self.pc) and not isinstance(self.pc, Constant):
            expression = self.pc
            taints = self.pc.taint

            def setstate(state, value):
                state.platform.current_vm.pc = BitVecConstant(256, value, taint=taints)

            raise Concretize("Concretice PC",
                             expression=expression,
                             setstate=setstate,
                             policy='ALL')
        #Fixme[felipe] add a with self.disabled_events context mangr to Eventful
        if self._on_transaction is False:
            self._publish('will_decode_instruction', self.pc)
        last_pc = self.pc
        current = self.instruction

        if self._on_transaction is False:
            self._publish('will_execute_instruction', self.pc, current)
        #Need to consume before potential out of stack exception
        old_gas = self._gas
        self._consume(current.fee)
        arguments = self._pop_arguments()
        result = None

        ex = None
        try:
            if self._on_transaction is False:
                self._publish('will_evm_execute_instruction', current, arguments)
            result = self._handler(*arguments)
        except ConcretizeStack as ex:
            #Revert the stack and gas so it looks like before executing the instruction
            self._push_arguments(arguments)
            self._gas = old_gas
            pos = -ex.pos

            def setstate(state, value):
                self.stack[pos] = value

            raise Concretize("Concretice Stack Variable",
                             expression=self.stack[pos],
                             setstate=setstate,
                             policy=ex.policy)
        except StartTx:
            #Revert the stack and gas so it looks like before executing the instruction
            self._push_arguments(arguments)
            self._gas = old_gas
            raise

        except EndTx as ex:
            #do not push result nor advance the pc
            if not current.is_branch:
                #advance pc pointer
                self.pc += self.instruction.size
            self._publish('did_evm_execute_instruction', current, arguments, Ref(result))
            self._publish('did_execute_instruction', last_pc, self.pc, current)
            raise

        if not current.is_branch:
            #advance pc pointer
            self.pc += self.instruction.size
        result_ref = Ref(result)
        self._publish('did_evm_execute_instruction', current, arguments, result_ref)
        self._publish('did_execute_instruction', last_pc, self.pc, current)

        self._push_results(current, result_ref.value)

    def read_buffer(self, offset, size):
        if issymbolic(size):
            raise EVMException("Symbolic size not supported")
        if size == 0:
            return bytearray()
        self._allocate(offset + size)
        return self.memory[offset: offset + size]

    def write_buffer(self, offset, data):
        self._allocate(offset + len(data))
        for i, c in enumerate(data):
            self._store(offset + i, Operators.ORD(c))

    def _load(self, offset, size=1):
        value = self.memory.read_BE(offset, size)
        try:
            value = simplify(value)
            if not value.taint:
                value = value.value
        except:
            pass

        for i in range(size):
            self._publish('did_evm_read_memory', offset + i, Operators.EXTRACT(value, (size - i - 1) * 8, 8))
        return value

    def _store(self, offset, value, size=1):
        ''' Stores value in memory as a big endian '''
        self.memory.write_BE(offset, value, size)
        for i in range(size):
            self._publish('did_evm_write_memory', offset + i, Operators.EXTRACT(value, (size - i - 1) * 8, 8))
    ############################################################################
    #INSTRUCTIONS

    def INVALID(self):
        '''Halts execution'''
        raise InvalidOpcode()

    ############################################################################
    # Stop and Arithmetic Operations
    # All arithmetic is modulo 256 unless otherwise noted.

    def STOP(self):
        ''' Halts execution '''
        raise EndTx('STOP')

    def ADD(self, a, b):
        ''' Addition operation '''
        return a + b

    def MUL(self, a, b):
        ''' Multiplication operation '''
        return a * b

    def SUB(self, a, b):
        ''' Subtraction operation '''
        return a - b

    def DIV(self, a, b):
        '''Integer division operation'''
        try:
            result = Operators.UDIV(a, b)
        except ZeroDivisionError:
            result = 0
        return Operators.ITEBV(256, b == 0, 0, result)

    def SDIV(self, a, b):
        '''Signed integer division operation (truncated)'''
        s0, s1 = to_signed(a), to_signed(b)
        try:
            result = (Operators.ABS(s0) // Operators.ABS(s1) * Operators.ITEBV(256, (s0 < 0) != (s1 < 0), -1, 1))
        except ZeroDivisionError:
            result = 0
        result = Operators.ITEBV(256, b == 0, 0, result)
        if not issymbolic(result):
            result = to_signed(result)
        return result

    def MOD(self, a, b):
        '''Modulo remainder operation'''
        try:
            result = Operators.ITEBV(256, b == 0, 0, a % b)
        except ZeroDivisionError:
            result = 0
        return result

    def SMOD(self, a, b):
        '''Signed modulo remainder operation'''
        s0, s1 = to_signed(a), to_signed(b)
        sign = Operators.ITEBV(256, s0 < 0, -1, 1)
        try:
            result = (Operators.ABS(s0) % Operators.ABS(s1)) * sign
        except ZeroDivisionError:
            result = 0

        return Operators.ITEBV(256, s1 == 0, 0, result)

    def ADDMOD(self, a, b, c):
        '''Modulo addition operation'''
        try:
            result = Operators.ITEBV(256, c == 0, 0, (a + b) % c)
        except ZeroDivisionError:
            result = 0
        return result

    def MULMOD(self, a, b, c):
        '''Modulo addition operation'''
        try:
            result = Operators.ITEBV(256, c == 0, 0, (a * b) % c)
        except ZeroDivisionError:
            result = 0
        return result

    def EXP(self, base, exponent):
        '''
            Exponential operation
            The zero-th power of zero 0^0 is defined to be one
        '''
        # fixme integer bitvec
        EXP_SUPPLEMENTAL_GAS = 50   # cost of EXP exponent per byte

        def nbytes(e):
            for i in range(32):
                if e >> (i * 8) == 0:
                    return i
            return 32
        self._consume(EXP_SUPPLEMENTAL_GAS * nbytes(exponent))
        return pow(base, exponent, TT256)

    def SIGNEXTEND(self, size, value):
        '''Extend length of two's complement signed integer'''
        # FIXME maybe use Operators.SEXTEND
        testbit = Operators.ITEBV(256, size <= 31, size * 8 + 7, 257)
        result1 = (value | (TT256 - (1 << testbit)))
        result2 = (value & ((1 << testbit) - 1))
        result = Operators.ITEBV(256, (value & (1 << testbit)) != 0, result1, result2)
        return Operators.ITEBV(256, size <= 31, result, value)

    ############################################################################
    # Comparison & Bitwise Logic Operations
    def LT(self, a, b):
        '''Less-than comparision'''
        return Operators.ITEBV(256, Operators.ULT(a, b), 1, 0)

    def GT(self, a, b):
        '''Greater-than comparision'''
        return Operators.ITEBV(256, Operators.UGT(a, b), 1, 0)

    def SLT(self, a, b):
        '''Signed less-than comparision'''
        # http://gavwood.com/paper.pdf
        s0, s1 = to_signed(a), to_signed(b)
        return Operators.ITEBV(256, s0 < s1, 1, 0)

    def SGT(self, a, b):
        '''Signed greater-than comparision'''
        # http://gavwood.com/paper.pdf
        s0, s1 = to_signed(a), to_signed(b)
        return Operators.ITEBV(256, s0 > s1, 1, 0)

    def EQ(self, a, b):
        '''Equality comparision'''
        return Operators.ITEBV(256, a == b, 1, 0)

    def ISZERO(self, a):
        '''Simple not operator'''
        return Operators.ITEBV(256, a == 0, 1, 0)

    def AND(self, a, b):
        '''Bitwise AND operation'''
        return a & b

    def OR(self, a, b):
        '''Bitwise OR operation'''
        return a | b

    def XOR(self, a, b):
        '''Bitwise XOR operation'''
        return a ^ b

    def NOT(self, a):
        '''Bitwise NOT operation'''
        return ~a

    def BYTE(self, offset, value):
        '''Retrieve single byte from word'''
        offset = Operators.ITEBV(256, offset < 32, (31 - offset) * 8, 256)
        return Operators.ZEXTEND(Operators.EXTRACT(value, offset, 8), 256)

    def SHA3(self, start, size):
        '''Compute Keccak-256 hash'''
        GSHA3WORD = 6         # Cost of SHA3 per word
        # read memory from start to end
        # calculate hash on it/ maybe remember in some structure where that hash came from
        # http://gavwood.com/paper.pdf
        if size:
            self._consume(GSHA3WORD * (ceil32(size) // 32))
        data = self.read_buffer(start, size)

        try:
            concrete_data = []
            for i in range(len(data)):
                try:
                    concrete_data.append(chr(simplify(data[i]).value))
                except:
                    pass
                    #simplify by solving. probably means that we need another simplification
                    s = solver.get_all_values(self.constraints, data, 2)
                    logger.debug("Simplifying by solving")  # :(
                    if len(s) == 1:
                        concrete_data.append(s[0])

            data = ''.join(concrete_data)
        except:
            pass

        if any(map(issymbolic, data)):
            return self.world.HASH(data)
        else:
            buf = ''.join(data)
            value = sha3.keccak_256(buf.encode()).hexdigest()
            value = int('0x' + value, 0)
            self._publish('on_concrete_sha3', buf, value)
            logger.info("Found a concrete SHA3 example %r -> %x", buf, value)
            return value

    ############################################################################
    # Environmental Information
    def ADDRESS(self):
        '''Get address of currently executing account'''
        return self.address

    def BALANCE(self, account):
        '''Get balance of the given account'''
        BALANCE_SUPPLEMENTAL_GAS = 380
        self._consume(BALANCE_SUPPLEMENTAL_GAS)
        return self.world.get_balance(account)

    def ORIGIN(self):
        '''Get execution origination address'''
        return self.world.tx_origin()

    def CALLER(self):
        '''Get caller address'''
        return Operators.ZEXTEND(self.caller, 256)

    def CALLVALUE(self):
        '''Get deposited value by the instruction/transaction responsible for this execution'''
        return self.value

    def CALLDATALOAD(self, offset):
        '''Get input data of current environment'''
        data_length = len(self.data)
        bytes = []
        for i in range(32):
            try:
                c = Operators.ITEBV(8, offset + i < data_length, self.data[offset + i], 0)
            except IndexError:
                # offset + i is concrete and outside data
                c = 0

            bytes.append(c)
        return Operators.CONCAT(256, *bytes)

    def CALLDATASIZE(self):
        '''Get size of input data in current environment'''
        return len(self.data)

    def safe_add(self, a, b):
        a = Operators.ZEXTEND(a, 512)
        b = Operators.ZEXTEND(b, 512)
        result = a + b
        self.constraints.add(Operators.UGE(result, 0))
        self.constraints.add(Operators.ULT(result, 1 << 256))
        return result

    def safe_mul(self, a, b):
        a = Operators.ZEXTEND(a, 512)
        b = Operators.ZEXTEND(b, 512)
        result = a * b
        self.constraints.add(Operators.UGE(result, 0))
        self.constraints.add(Operators.ULT(result, 1 << 256))
        return result

    def CALLDATACOPY(self, mem_offset, data_offset, size):
        '''Copy input data in current environment to memory'''
        GCOPY = 3             # cost to copy one 32 byte word
        old_gas = self.gas

        self._consume(self.safe_mul(GCOPY, self.safe_add(size, 31) // 32))
        self._allocate(self.safe_add(mem_offset, size))

        # slow debug check
        #if issymbolic(size):
        #    assert not solver.can_be_true(self.constraints, Operators.UGT(self.gas, old_gas))

        if issymbolic(size):
            #self.constraints.add(size % 32 == 0)
            #self.constraints.add(Operators.ULT(size, 32 * 10))
            raise ConcretizeStack(3, policy='SAMPLED')

        for i in range(size):
            try:
                c = Operators.ITEBV(8, data_offset + i < len(self.data), Operators.ORD(self.data[data_offset + i]), 0)
            except IndexError:
                # data_offset + i is concrete and outside data
                c = 0
            self._store(mem_offset + i, c)

    def CODESIZE(self):
        '''Get size of code running in current environment'''
        return len(self.bytecode)

    def CODECOPY(self, mem_offset, code_offset, size):
        '''Copy code running in current environment to memory'''

        self._allocate(mem_offset + size)

        if issymbolic(size):
            max_size = solver.max(self.constraints, size)
        else:
            max_size = size

        for i in range(max_size):
            if issymbolic(i < size):
                default = Operators.ITEBV(256, i < size, 0, self._load(mem_offset + i))  # Fixme. unnecessary memory read
            else:
                if i < size:
                    default = 0
                else:
                    default = self._load(mem_offset + i)

            if issymbolic(code_offset):
                value = Operators.ITEBV(256, code_offset + i >= len(self.bytecode), default, self.bytecode[code_offset + i])
            else:
                if code_offset + i >= len(self.bytecode):
                    value = default
                else:
                    value = self.bytecode[code_offset + i]

            self._store(mem_offset + i, value)
        self._publish('did_evm_read_code', code_offset, size)

    def GASPRICE(self):
        '''Get price of gas in current environment'''
        return self.world.tx_gasprice()

    @concretized_args(account='ACCOUNTS')
    def EXTCODESIZE(self, account):
        '''Get size of an account's code'''
        return len(self.world.get_code(account))

    @concretized_args(account='ACCOUNTS')
    def EXTCODECOPY(self, account, address, offset, size):
        '''Copy an account's code to memory'''
        extbytecode = self.world.get_code(account)
        GCOPY = 3             # cost to copy one 32 byte word
        self._consume(GCOPY * ceil32(len(extbytecode)) // 32)

        self._allocate(address + size)

        for i in range(size):
            if offset + i < len(extbytecode):
                self._store(address + i, extbytecode[offset + i])
            else:
                self._store(address + i, 0)

    def RETURNDATACOPY(self, mem_offset, return_offset, size):
        return_data = self.world.last_transaction.return_data

        self._allocate(mem_offset + size)
        for i in range(size):
            if return_offset + i < len(return_data):
                self._store(mem_offset + i, return_data[return_offset + i])
            else:
                self._store(mem_offset + i, 0)

    def RETURNDATASIZE(self):
        return len(self.world.last_transaction.return_data)

    ############################################################################
    # Block Information
    def BLOCKHASH(self, a):
        '''Get the hash of one of the 256 most recent complete blocks'''
        return self.world.block_hash(a)

    def COINBASE(self):
        '''Get the block's beneficiary address'''
        return self.world.block_coinbase()

    def TIMESTAMP(self):
        '''Get the block's timestamp'''
        return self.world.block_timestamp()

    def NUMBER(self):
        '''Get the block's number'''
        return self.world.block_number()

    def DIFFICULTY(self):
        '''Get the block's difficulty'''
        return self.world.block_difficulty()

    def GASLIMIT(self):
        '''Get the block's gas limit'''
        return self.world.block_gaslimit()

    ############################################################################
    # Stack, Memory, Storage and Flow Operations
    def POP(self, a):
        '''Remove item from stack'''
        # Items are automatically removed from stack
        # by the instruction dispatcher
        pass

    def MLOAD(self, address):
        '''Load word from memory'''
        self._allocate(address + 32)
        value = self._load(address, 32)
        return value

    def MSTORE(self, address, value):
        '''Save word to memory'''
        if istainted(self.pc):
            for taint in get_taints(self.pc):
                value = taint_with(value, taint)
        self._allocate(address + 32)
        self._store(address, value, 32)

    def MSTORE8(self, address, value):
        '''Save byte to memory'''
        if istainted(self.pc):
            for taint in get_taints(self.pc):
                value = taint_with(value, taint)
        self._allocate(address)
        self._store(address, value, 1)

    def SLOAD(self, offset):
        '''Load word from storage'''
        storage_address = self.address
        self._publish('will_evm_read_storage', storage_address, offset)
        value = self.world.get_storage_data(storage_address, offset)
        self._publish('did_evm_read_storage', storage_address, offset, value)
        return value

    def SSTORE(self, offset, value):
        '''Save word to storage'''
        storage_address = self.address
        self._publish('will_evm_write_storage', storage_address, offset, value)
        if istainted(self.pc):
            for taint in get_taints(self.pc):
                value = taint_with(value, taint)
        self.world.set_storage_data(storage_address, offset, value)
        self._publish('did_evm_write_storage', storage_address, offset, value)

    def JUMP(self, dest):
        '''Alter the program counter'''
        self.pc = dest
        # TODO check for JUMPDEST on next iter?

    def JUMPI(self, dest, cond):
        '''Conditionally alter the program counter'''
        self.pc = Operators.ITEBV(256, cond != 0, dest, self.pc + self.instruction.size)

    def GETPC(self):
        '''Get the value of the program counter prior to the increment'''
        return self.pc

    def MSIZE(self):
        '''Get the size of active memory in bytes'''
        return self._allocated

    def GAS(self):
        '''Get the amount of available gas, including the corresponding reduction the amount of available gas'''
        #fixme calculate gas consumption
        return self._gas

    def JUMPDEST(self):
        '''Mark a valid destination for jumps'''

    ############################################################################
    # Push Operations
    def PUSH(self, value):
        '''Place 1 to 32 bytes item on stack'''
        return value

    ############################################################################
    # Duplication Operations
    def DUP(self, *operands):
        '''Duplicate stack item'''
        return (operands[-1],) + operands

    ############################################################################
    # Exchange Operations
    def SWAP(self, *operands):
        '''Exchange 1st and 2nd stack items'''
        a = operands[0]
        b = operands[-1]
        return (b,) + operands[1:-1] + (a,)

    ############################################################################
    # Logging Operations
    @concretized_args(size='ONE')
    def LOG(self, address, size, *topics):
        memlog = self.read_buffer(address, size)
        self.world.log(self.address, topics, memlog)

    ############################################################################
    # System operations
    @transact
    def CREATE(self, value, offset, size):
        '''Create a new account with associated code'''
        address = self.world.create_account()
        self.world.start_transaction('CREATE',
                                     address,
                                     data=self.read_buffer(offset, size),
                                     caller=self.address,
                                     value=value,
                                     gas=self.gas)
        raise StartTx()

    @CREATE.pos
    def CREATE(self, value, offset, size):
        '''Create a new account with associated code'''
        tx = self.world.last_transaction  # At this point last and current tx are the same.
        address = tx.address
        if tx.result == 'RETURN':
            self.world.set_code(tx.address, tx.return_data)
        else:
            self.world.delete_account(address)
            address = 0
        return address

    @transact
    @concretized_args(address='ACCOUNTS', gas='MINMAX', in_offset='SAMPLED', in_size='SAMPLED')
    def CALL(self, gas, address, value, in_offset, in_size, out_offset, out_size):
        '''Message-call into an account'''
        self.world.start_transaction('CALL',
                                     address,
                                     data=self.read_buffer(in_offset, in_size),
                                     caller=self.address,
                                     value=value,
                                     gas=gas)
        raise StartTx()

    @CALL.pos
    def CALL(self, gas, address, value, in_offset, in_size, out_offset, out_size):
        data = self.world.last_transaction.return_data
        if data is not None:
            data_size = len(data)
            size = Operators.ITEBV(256, Operators.ULT(out_size, data_size), out_size, data_size)
            self.write_buffer(out_offset, data[:size])

        return self.world.last_transaction.return_value

    @transact
    @concretized_args(in_offset='SAMPLED', in_size='SAMPLED')
    def CALLCODE(self, gas, _ignored_, value, in_offset, in_size, out_offset, out_size):
        '''Message-call into this account with alternative account's code'''
        self.world.start_transaction('CALL',
                                     address=self.address,
                                     data=self.read_buffer(in_offset, in_size),
                                     caller=self.address,
                                     value=value,
                                     gas=self.gas)
        raise StartTx()

    @CALLCODE.pos
    def CALLCODE(self, gas, address, value, in_offset, in_size, out_offset, out_size):
        data = self.world.last_transaction.return_data
        if data is not None:
            data_size = len(data)
            size = Operators.ITEBV(256, Operators.ULT(out_size, data_size), out_size, data_size)
            self.write_buffer(out_offset, data[:size])

        return self.world.last_transaction.return_value

    def RETURN(self, offset, size):
        '''Halt execution returning output data'''
        data = self.read_buffer(offset, size)
        raise EndTx('RETURN', data)

    @transact
    @concretized_args(in_offset='SAMPLED', in_size='SAMPLED')
    def DELEGATECALL(self, gas, address, in_offset, in_size, out_offset, out_size):
        '''Message-call into an account'''
        self.world.start_transaction('DELEGATECALL',
                                     address,
                                     data=self.read_buffer(in_offset, in_size),
                                     caller=self.address,
                                     value=0,
                                     gas=self.gas)
        raise StartTx()

    @DELEGATECALL.pos
    def DELEGATECALL(self, gas, address, in_offset, in_size, out_offset, out_size):
        data = self.world.last_transaction.return_data
        if data is not None:
            data_size = len(data)
            size = Operators.ITEBV(256, Operators.ULT(out_size, data_size), out_size, data_size)
            self.write_buffer(out_offset, data[:size])

        return self.world.last_transaction.return_value

    @transact
    @concretized_args(in_offset='SAMPLED', in_size='SAMPLED')
    def STATICCALL(self, gas, address, in_offset, in_size, out_offset, out_size):
        '''Message-call into an account'''
        self.world.start_transaction('STATICCALL',
                                     address,
                                     data=self.read_buffer(in_offset, in_size),
                                     caller=self.address,
                                     value=0,
                                     gas=self.gas)
        raise StartTx()

    @STATICCALL.pos
    def STATICCALL(self, gas, address, in_offset, in_size, out_offset, out_size):
        data = self.world.last_transaction.return_data
        if data is not None:
            data_size = len(data)
            size = Operators.ITEBV(256, Operators.ULT(out_size, data_size), out_size, data_size)
            self.write_buffer(out_offset, data[:size])

        return self.world.last_transaction.return_value

    def REVERT(self, offset, size):
        data = self.read_buffer(offset, size)
        #FIXME return remaining gas
        raise EndTx('REVERT', data)

    def THROW(self):
        #revert balance on CALL fail
        raise EndTx('THROW')

    def SELFDESTRUCT(self, recipient):
        '''Halt execution and register account for later deletion'''
        #This may create a user account
        recipient = Operators.EXTRACT(recipient, 0, 160)
        address = self.address

        #FIXME for on the known addresses
        if issymbolic(recipient):
            logger.info("Symbolic recipient on self destruct")
            recipient = solver.get_value(self.constraints, recipient)

        if recipient not in self.world:
            self.world.create_account(address=recipient, balance=0, code='', storage=None)

        self.world.send_funds(address, recipient, self.world.get_balance(address))
        self.world.delete_account(address)

        raise EndTx('SELFDESTRUCT')

    def __str__(self):
        def hexdump(src, length=16):
            FILTER = ''.join([(len(repr(chr(x))) == 3) and chr(x) or '.' for x in range(256)])
            lines = []
            for c in range(0, len(src), length):
                chars = src[c:c + length]

                def p(x):
                    if issymbolic(x):
                        return '??'
                    else:
                        return "%02x" % x
                hex = ' '.join([p(x) for x in chars])

                def p1(x):
                    if issymbolic(x):
                        return '.'
                    else:
                        return "%s" % ((x <= 127 and FILTER[x]) or '.')

                printable = ''.join([p1(x) for x in chars])
                lines.append("%04x  %-*s  %s" % (c, length * 3, hex, printable))
            return lines

        m = []
        for offset in range(128):
            c = simplify(self.memory[offset])
            try:
                c = c.value
            except:
                pass
            m.append(c)

        hd = hexdump(m)

        #hd = ''  # str(self.memory)
        result = ['-' * 147]
        pc = self.pc
        if isinstance(self.pc, Constant):
            pc = self.pc.value

        if issymbolic(pc):
            result.append('<Symbolic PC>')

        else:
            result.append('0x%04x: %s %s %s\n' % (pc, self.instruction.name, self.instruction.has_operand and '0x%x' %
                                                  self.instruction.operand or '', self.instruction.description))

        result.append('Stack                                                                      Memory')
        sp = 0
        for i in list(reversed(self.stack))[:10]:
            r = ''
            if issymbolic(i):
                r = '%s %r' % (sp == 0 and 'top> ' or '     ', i)
            else:
                r = '%s 0x%064x' % (sp == 0 and 'top> ' or '     ', i)
            sp += 1

            h = ''
            try:
                h = hd[sp - 1]
            except BaseException:
                pass
            r += ' ' * (75 - len(r)) + h
            result.append(r)

        for i in range(sp, len(hd)):
            r = ' ' * 75 + hd[i]
            result.append(r)

        result = [hex(self.address) + ": " + x for x in result]
        return '\n'.join(result)

################################################################################
################################################################################
################################################################################
################################################################################


class EVMWorld(Platform):
    _published_events = {'evm_read_storage', 'evm_write_storage', 'evm_read_code',
                         'decode_instruction', 'execute_instruction', 'concrete_sha3', 'symbolic_sha3',
                         'open_transaction', 'close_transaction'}

    def __init__(self, constraints, storage=None, initial_block_number=None, initial_timestamp=None, **kwargs):
        super().__init__(path="NOPATH", **kwargs)
        self._world_state = {} if storage is None else storage
        self._constraints = constraints
        self._callstack = []
        self._deleted_accounts = []
        self._logs = list()
        self._sha3 = {}
        self._pending_transaction = None
        self._transactions = list()

        if initial_block_number is None:
            #assume initial symbolic block
            initial_block_number = constraints.new_bitvec(256, "BLOCKNUMBER")
        self._initial_block_number = initial_block_number
        if initial_timestamp is None:
            #1524785992; // Thu Apr 26 23:39:52 UTC 2018
            initial_timestamp = constraints.new_bitvec(256, "TIMESTAMP")
            constraints.add(Operators.UGT(initial_timestamp, 1000000000))
            constraints.add(Operators.ULT(initial_timestamp, 3000000000))
        self._initial_timestamp = initial_timestamp

        self._do_events()
        '''
        for var_i in range(5):
            for offset_i in range(10):
                data = ("%064x%064x" % (var_i, offset_i)).decode('hex')
                value = int(sha3.keccak_256(data).hexdigest(), 16)
                self._concrete_sha3_callback(data, value)
                for offset_j in range(10):
                    data = ("%064x" % offset_j).decode('hex') + data
                    value = int(sha3.keccak_256(data).hexdigest(), 16)
                    self._concrete_sha3_callback(data, value)
        '''

    def __getstate__(self):
        state = super().__getstate__()
        state['sha3'] = self._sha3
        state['pending_transaction'] = self._pending_transaction
        state['logs'] = self._logs
        state['world_state'] = self._world_state
        state['constraints'] = self._constraints
        state['callstack'] = self._callstack
        state['deleted_accounts'] = self._deleted_accounts
        state['transactions'] = self._transactions
        state['initial_block_number'] = self._initial_block_number
        state['_initial_timestamp'] = self._initial_timestamp
        return state

    def __setstate__(self, state):
        super().__setstate__(state)
        self._constraints = state['constraints']
        self._sha3 = state['sha3']
        self._pending_transaction = state['pending_transaction']
        self._world_state = state['world_state']
        self._deleted_accounts = state['deleted_accounts']
        self._logs = state['logs']
        self._callstack = state['callstack']
        self._transactions = state['transactions']
        self._initial_block_number = state['initial_block_number']
        self._initial_timestamp = state['_initial_timestamp']
        self._do_events()

    def _do_events(self):
        if self.current_vm is not None:
            self.forward_events_from(self.current_vm)
            self.subscribe('on_concrete_sha3', self._concrete_sha3_callback)

    def _concrete_sha3_callback(self, buf, value):
        buf = str(buf)
        if buf in self._sha3:
            assert self._sha3[buf] == value
        self._sha3[buf] = value

    def __getitem__(self, index):
        assert isinstance(index, int)
        return self._world_state[index]

    def __contains__(self, key):
        assert not issymbolic(key), "Symbolic address not supported"
        return key in self.accounts

    def __str__(self):
        return "WORLD:" + str(self._world_state)

    @property
    def logs(self):
        return self._logs

    @property
    def constraints(self):
        return self._constraints

    def _open_transaction(self, sort, address, price, bytecode_or_data, caller, value, gas=2300):

        if self.depth > 0:
            origin = self.tx_origin()
        else:
            origin = caller
        assert price is not None

        tx = Transaction(sort, address, price, bytecode_or_data, caller, value, depth=self.depth, gas=gas)
        if sort == 'CREATE':
            bytecode = bytecode_or_data
            data = bytearray()
        else:
            bytecode = self.get_code(address)
            data = bytecode_or_data

        address = tx.address
        if tx.sort == 'DELEGATECALL':
            address = tx.caller
            assert value == 0

        vm = EVM(self._constraints, address, data, caller, value, bytecode, world=self)

        self._publish('will_open_transaction', tx)
        self._callstack.append((tx, self.logs, self.deleted_accounts, copy.copy(self.get_storage(address)), vm))
        self._publish('did_open_transaction', tx)

        self._do_events()

    def _close_transaction(self, result, data=None, rollback=False):
        self._publish('will_close_transaction', self._callstack[-1][0])
        tx, logs, deleted_accounts, account_storage, vm = self._callstack.pop()
        assert self.constraints == vm.constraints
        # Keep constraints gathered in the last vm
        self.constraints = vm.constraints

        if rollback:
            for address, account in self._deleted_accounts:
                self._world_state[address] = account

            self._set_storage(vm.address, account_storage)
            self._deleted_accounts = self._deleted_accounts
            self._logs = logs
            self.send_funds(tx.address, tx.caller, tx.value)

        tx.set_result(result, data)
        self._transactions.append(tx)

        self._publish('did_close_transaction', tx)

        if self.depth == 0:
            raise TerminateState(tx.result)

    @property
    def all_transactions(self):
        txs = tuple(self._transactions)
        return txs + tuple((x[0] for x in reversed(self._callstack)))

    @property
    def transactions(self):
        ''' Completed completed transaction '''
        return tuple((tx for tx in self._transactions if tx.result != 'TXERROR'))

    @property
    def human_transactions(self):
        ''' Completed human transaction '''
        txs = []
        for tx in self.transactions:
            if tx.depth == 0:
                txs.append(tx)
        return tuple(txs)

    @property
    def last_transaction(self):
        ''' Last completed transaction '''
        if len(self.transactions):
            return self.transactions[-1]
        return None

    @property
    def last_human_transaction(self):
        ''' Last completed human transaction '''
        for tx in reversed(self.transactions):
            if tx.depth == 0:
                return tx
        return None

    @constraints.setter
    def constraints(self, constraints):
        self._constraints = constraints
        if self.current_vm:
            self.current_vm.constraints = constraints

    @property
    def current_vm(self):
        """ current vm """
        try:
            _, _, _, _, vm = self._callstack[-1]
            return vm
        except IndexError:
            return None

    @property
    def current_transaction(self):
        """ current tx """
        try:
            tx, _, _, _, _ = self._callstack[-1]
            if tx.result is not None:
                #That tx finished. No current tx.
                return None
            return tx
        except IndexError:
            return None

    @property
    def current_human_transaction(self):
        ''' Current ongoing human transaction '''
        try:
            tx, _, _, _, _ = self._callstack[0]
            if tx.result is not None:
                #That tx finished. No current tx.
                return None
            assert tx.depth == 0
            return tx
        except IndexError:
            return None

    @property
    def accounts(self):
        return list(self._world_state.keys())

    @property
    def normal_accounts(self):
        accs = []
        for address in self.accounts:
            if len(self.get_code(address)) == 0:
                accs.append(address)
        return accs

    @property
    def contract_accounts(self):
        accs = []
        for address in self.accounts:
            if len(self.get_code(address)) > 0:
                accs.append(address)
        return accs

    @property
    def deleted_accounts(self):
        return self._deleted_accounts

    def delete_account(self, address):
        if address in self._world_state:
            deleted_account = (address, self._world_state[address])
            del self._world_state[address]
            self._deleted_accounts.append(deleted_account)

    def get_storage_data(self, storage_address, offset):
        """
        Read a value from a storage slot on the specified account

        :param storage_address: an account address
        :param offset: the storage slot to use.
        :type offset: int or BitVec
        :return: the value
        :rtype: int or BitVec
        """
        value = self._world_state[storage_address]['storage'].get(offset, 0)
        return simplify(value)

    def set_storage_data(self, storage_address, offset, value):
        """
        Writes a value to a storage slot in specified account

        :param storage_address: an account address
        :param offset: the storage slot to use.
        :type offset: int or BitVec
        :param value: the value to write
        :type value: int or BitVec
        """
        self._world_state[storage_address]['storage'][offset] = value

    def get_storage_items(self, address):
        """


        :param address: account address
        :return: all items in account storage. items are tuple of (index, value). value can be symbolic
        :rtype: list[(storage_index, storage_value)]
        """
        storage = self._world_state[address]['storage']
        items = []
        array = storage.array
        while not isinstance(array, ArrayVariable):
            items.append((array.index, array.value))
            array = array.array
        return items

    def has_storage(self, address):
        """
        True if something has been written to the storage.
        Note that if a slot has been erased from the storage this function may
        lose any meaning.
        """
        storage = self._world_state[address]['storage']
        array = storage.array
        while not isinstance(array, ArrayVariable):
            if isinstance(array, ArrayStore):
                return True
            array = array.array
        return False

    def get_storage(self, address):
        """

        :param address: account address
        :return: account storage
        :rtype: bytearray or ArrayProxy
        """
        return self._world_state[address]['storage']

    def _set_storage(self, address, storage):
        """ Private auxiliar function to replace the storage """
        self._world_state[address]['storage'] = storage

    def set_balance(self, address, value):
        self._world_state[int(address)]['balance'] = value

    def get_balance(self, address):
        if address not in self._world_state:
            return 0
        return self._world_state[address]['balance']

    def add_to_balance(self, address, value):
        assert address in self._world_state
        self._world_state[address]['balance'] += value

    def send_funds(self, sender, recipient, value):
        self._world_state[sender]['balance'] -= value
        self._world_state[recipient]['balance'] += value

    def get_code(self, address):
        if address not in self._world_state:
            return bytearray()
        return self._world_state[address]['code']

    def set_code(self, address, data):
        assert data is not None
        if self._world_state[address]['code']:
            raise EVMException("Code already set")
        self._world_state[address]['code'] = data

    def has_code(self, address):
        return len(self._world_state[address]['code']) > 0

    def log(self, address, topics, data):
        self._logs.append(EVMLog(address, data, topics))
        logger.info('LOG %r %r', data, topics)

    def log_storage(self, addr):
        pass

    def add_refund(self, value):
        pass

    def block_prevhash(self):
        return 0

    def block_coinbase(self):
        return 0

    def block_timestamp(self):
        return self._initial_timestamp + len(self.human_transactions)

    def block_number(self):
        return self._initial_block_number + len(self.human_transactions)

    def block_difficulty(self):
        return 0

    def block_gaslimit(self):
        return 0

    def block_hash(self, block_number=None, force_recent=True):
        ''' Calculates a block's hash
            :param block_number: the block number for which to calculate the hash, defaulting to the most recent block
            :param force_recent: if True (the default) return zero for any block that is in the future or older than 256 blocks
            :return: the block hash
        '''
        if block_number is None:
            block_number = self.block_number() - 1

        # We are not maintaining an actual -block-chain- so we just generate
        # some hashes for each virtual block
        value = sha3.keccak_256(repr(block_number) + 'NONCE').hexdigest()
        value = int('0x' + value, 0)

        if force_recent:
            # 0 is left on the stack if the looked for block number is greater or equal
            # than the current block number or more than 256 blocks behind the current
            # block. (Current block hash is unknown from inside the tx)
            bnmax = Operators.ITEBV(256, self.block_number() > 256, 256, self.block_number())
            value = Operators.ITEBV(256, Operators.OR(block_number >= self.block_number(), block_number < bnmax), 0, value)

        return value

    def tx_origin(self):
        if self.current_human_transaction:
            return self.current_human_transaction.caller

    def tx_gasprice(self):
        if self.current_human_transaction:
            return self.current_human_transaction.price

    @property
    def depth(self):
        return len(self._callstack)

    def new_address(self):
        ''' Create a fresh 160bit address '''
        # Fix use more yellow solution
        new_address = random.randint(100, pow(2, 160))
        if new_address in self:
            return self.new_address()
        return new_address

    def execute(self):
        self._process_pending_transaction()
        if self.current_vm is None:
            raise TerminateState("Trying to execute an empty transaction", testcase=False)
        try:
            self.current_vm.execute()
        except StartTx:
            pass
        except EndTx as ex:
            self._close_transaction(ex.result, ex.data, rollback=ex.is_rollback())

    def create_account(self, address=None, balance=0, code='', storage=None, nonce=0):
        ''' code is the runtime code '''
        if storage is None:
            storage = self.constraints.new_array(index_bits=256, value_bits=256, name='STORAGE')

        if address is None:
            address = self.new_address()
        if address in self.accounts:
            # FIXME account may have been created via selfdestruct destinatary
            # or CALL and may contain some ether already. Though if it was a
            # selfdestroyed address it can not be reused
            raise EthereumError('The account already exists')
        if code is None:
            code = bytearray()
        self._world_state[address] = {}
        self._world_state[address]['nonce'] = 0
        self._world_state[address]['balance'] = balance
        self._world_state[address]['storage'] = storage
        self._world_state[address]['code'] = code
        return address

    def create_contract(self, price=0, address=None, caller=None, balance=0, init=None):
        '''
        The way that the Solidity compiler expects the constructor arguments to
        be passed is by appending the arguments to the byte code produced by the
        Solidity compiler. The arguments are formatted as defined in the Ethereum
        ABI2. The arguments are then copied from the init byte array to the EVM
        memory through the CODECOPY opcode with appropriate values on the stack.
        This is done when the byte code in the init byte array is actually run
        on the network.
        '''
        address = self.create_account(address)
        self.start_transaction('CREATE', address, price, init, caller, balance)
        self._process_pending_transaction()
        return address

    def transaction(self, address, price=0, data='', caller=None, value=0):
        self.start_transaction('CALL', address, price=price, data=data, caller=caller, value=value)
        self._process_pending_transaction()

    def start_transaction(self, sort, address, price=None, data=None, caller=None, value=0, gas=2300):
        ''' Initiate a transaction
            :param sort: the type of transaction. CREATE or CALL or DELEGATECALL
            :param address: the address of the account which owns the code that is executing.
            :param price: the price of gas in the transaction that originated this execution.
            :param data: the byte array that is the input data to this execution
            :param caller: the address of the account which caused the code to be executing. A 160-bit code used for identifying Accounts
            :param value: the value, in Wei, passed to this account as part of the same procedure as execution. One Ether is defined as being 10**18 Wei.
            :param bytecode: the byte array that is the machine code to be executed.
            :param gas: gas budget for this transaction.

        '''
        assert self._pending_transaction is None, "Already started tx"
        self._pending_transaction = PendingTransaction(sort, address, price, data, caller, value, gas)

    def _constraint_to_accounts(self, address, include_zero=False, ty='both'):
            if ty not in ('both', 'normal', 'contract'):
                raise ValueError('Bad account type. It must be `normal`, `contract` or `both`')
            if ty == 'both':
                accounts = self.accounts
            elif ty == 'normal':
                accounts = self.normal_accounts
            else:
                assert ty == 'contract'
                accounts = self.contract_accounts

            #Constraint it so it can range over all accounts + address0
            cond = True
            if accounts:
                cond = None
                if include_zero:
                    cond = address == 0

                for known_account in accounts:
                    if cond is None:
                        cond = address == known_account
                    else:
                        cond = Operators.OR(address == known_account, cond)
            return cond

    def _pending_transaction_concretize_address(self):
        sort, address, price, data, caller, value, gas = self._pending_transaction
        if issymbolic(address):
            def set_address(state, solution):
                world = state.platform
                world._pending_transaction = sort, solution, price, data, caller, value, gas
            cond = self._constraint_to_accounts(address, ty='contract', include_zero=False)
            self.constraints.add(cond)
            raise Concretize('Concretizing address on transaction',
                             expression=address,
                             setstate=set_address,
                             policy='ALL')

    def _pending_transaction_concretize_caller(self):
        sort, address, price, data, caller, value, gas = self._pending_transaction
        if issymbolic(caller):
            def set_caller(state, solution):
                world = state.platform
                world._pending_transaction = sort, address, price, data, solution, value, gas
            #Constraint it so it can range over all normal accounts
            cond = self._constraint_to_accounts(caller, ty='normal')
            self.constraints.add(cond)
            raise Concretize('Concretizing caller on transaction',
                             expression=caller,
                             setstate=set_caller,
                             policy='ALL')

    def _process_pending_transaction(self):
        # Nothing to do here if no pending transactions
        if self._pending_transaction is None:
            return
        sort, address, price, data, caller, value, gas = self._pending_transaction

        if sort not in {'CALL', 'CREATE', 'DELEGATECALL'}:
            raise EVMException('Type of transaction not supported')

        if self.depth > 0:
            price = self.tx_gasprice()
        if price is None:
            raise EVMException("Need to set a gas price on human tx")

        self._pending_transaction_concretize_address()
        self._pending_transaction_concretize_caller()
        if caller not in self.accounts:
            raise EVMException('Caller account does not exist')

        if address not in self.accounts:
            # Creating a unaccessible account
            self.create_account(address=address)

        # Check depth
        failed = self.depth > 1024

        # Fork on enough funds
        if not failed:
            src_balance = self.get_balance(caller)
            enough_balance = src_balance >= value
            if issymbolic(enough_balance):
                self.constraints.add(src_balance + value >= src_balance)
            enough_balance_solutions = solver.get_all_values(self._constraints, enough_balance)

            if set(enough_balance_solutions) == {True, False}:
                raise Concretize('Forking on available funds',
                                 expression=src_balance < value,
                                 setstate=lambda a, b: None,
                                 policy='ALL')
            failed = set(enough_balance_solutions) == {False}

        #processed
        self._pending_transaction = None

        #Here we have enough funds and room in the callstack
        self.send_funds(caller, address, value)

        self._open_transaction(sort, address, price, data, caller, value, gas=gas)

        if failed:
            self._close_transaction('TXERROR', rollback=True)

        #Transaction to normal account
        if sort in ('CALL', 'DELEGATECALL') and not self.get_code(address):
            self._close_transaction('STOP')

    def HASH(self, data):
        def compare_buffers(a, b):
            if len(a) != len(b):
                return False
            cond = True
            for i in range(len(a)):
                cond = Operators.AND(a[i] == b[i], cond)
                if cond is False:
                    return False
            return cond

        assert any(map(issymbolic, data))
        logger.info("SHA3 Searching over %d known hashes", len(self._sha3))
        logger.info("SHA3 TODO save this state for future explorations with more known hashes")
        # Broadcast the signal
        self._publish('on_symbolic_sha3', data, list(self._sha3.items()))
        results = []

        # If know_hashes is true then there is a _known_ solution for the hash
        known_hashes = False
        for key, value in self._sha3.items():
            assert not any(map(issymbolic, key)), "Saved sha3 data,hash pairs should be concrete"
            cond = compare_buffers(key, data)
            if solver.can_be_true(self._constraints, cond):
                results.append((cond, value))
                known_hashes = Operators.OR(cond, known_hashes)

        # results contains all the possible and known solutions

        # If known_hashes can be False then data can take at least one concrete
        # value of which we do not know a hash for.

        # Calculate the sha3 of one extra example solution and add this as a
        # potential result
        # This is an incomplete result:
        # Intead of choosing one single extra concrete solution we should save
        # the state and when a new sha3 example is found load it back and try
        # the new concretization for sha3.

        with self._constraints as temp_cs:
            if solver.can_be_true(temp_cs, Operators.NOT(known_hashes)):
                temp_cs.add(Operators.NOT(known_hashes))
                # a_buffer is different from all strings we know a hash for
                a_buffer = solver.get_value(temp_cs, data)
                cond = compare_buffers(a_buffer, data)
                # Get the sha3 for a_buffer
                a_value = int(sha3.keccak_256(a_buffer).hexdigest(), 16)
                # add the new sha3 pair to the known_hashes and result
                self._publish('on_concrete_sha3', a_buffer, a_value)
                results.append((cond, a_value))
                known_hashes = Operators.OR(cond, known_hashes)

        if solver.can_be_true(self._constraints, known_hashes):
            self._constraints.add(known_hashes)
            value = 0  # never used
            for cond, sha in results:
                value = Operators.ITEBV(256, cond, sha, value)
        else:
            raise TerminateState("Unknown hash")

        return value
