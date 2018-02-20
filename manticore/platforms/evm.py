''' Symbolic EVM implementation based on the yellow paper: http://gavwood.com/paper.pdf '''
import random, copy
from ..utils.helpers import issymbolic, memoized
from ..platforms.platform import *
from ..core.smtlib import solver, TooManySolutions, Expression, Bool, BitVec, Array, Operators, Constant, BitVecConstant, ConstraintSet, \
    SolverException
from ..core.state import ForkState, TerminateState
from ..utils.event import Eventful
from ..core.smtlib.visitors import pretty_print, arithmetic_simplifier, translate_to_smtlib
from ..core.state import Concretize,TerminateState
import logging
import sys, hashlib
if sys.version_info < (3, 6):
    import sha3

logger = logging.getLogger(__name__)

# Auxiliar constants and functions
TT256 = 2 ** 256
TT256M1 = 2 ** 256 - 1
TT255 = 2 ** 255
TOOHIGHMEM = 0x1000

def ceil32(x):
    return Operators.ITEBV(256, (x % 32) == 0, x , x + 32 - (x % 32))

def to_signed(i):
    return Operators.ITEBV(256, i<TT255, i, i-TT256)

class Transaction(object):
    __slots__= 'sort', 'address', 'origin', 'price', 'data', 'caller', 'value', 'return_data', 'result'
    def __init__(self, sort, address, origin, price, data, caller, value, return_data, result):
        self.sort = sort
        self.address = address
        self.origin = origin
        self.price = price
        self.data = data
        self.caller = caller
        self.value = value
        self.return_data = return_data
        self.result = result

    def __reduce__(self):
        ''' Implements serialization/pickle '''
        return (self.__class__,  (self.sort,  self.address, self.origin, self.price, self.data, self.caller, self.value, self.return_data, self.result))

    def __str__(self):
        return 'Transaction(%s, from=0x%x, to=0x%x, value=%r, data=%r..)' %(self.sort, self.caller, self.address, self.value, self.data)

class EVMLog():
    def __init__(self, address, memlog, topics):
        self.address = address
        self.memlog = memlog
        self.topics = topics



class EVMMemory(object):
    def __init__(self, constraints, address_size=256, value_size=8, *args, **kwargs):
        '''
        A symbolic memory manager for EVM. 
        This is internally used to provide memory to an Ethereum Virtual Machine.
        It maps address_size bits wide bitvectors to value_size wide bitvectors.
        Normally BitVec(256) -> BitVec(8)

        Example use::
            cs = ConstraintSet()
            mem = EVMMemory(cs)
            mem[16] = 0x41
            assert (mem.allocated == 1)
            assert (mem[16] == 0x41)

        :param constraints: a set of constraints
        :type constraints: ConstraintSet
        :param address_size: address bit width
        :param values_size: value bit width
        '''
        assert isinstance(constraints, (ConstraintSet, type(None)))
        self._constraints = constraints
        self._symbols = {}
        self._memory = {}
        self._address_size=address_size
        self._value_size=value_size
        self._allocated = 0

    def __copy__(self):
        ''' Makes a copy of itself '''
        new_mem = EVMMemory(self._constraints, self._address_size,  self._value_size)
        new_mem._memory = dict(self._memory)
        new_mem._symbols = dict(self._symbols)
        return new_mem

    def __reduce__(self):
        ''' Implements serialization/pickle '''
        return (self.__class__, (self._constraints, self._address_size,  self._value_size), {'_symbols':self._symbols, '_memory':self._memory, '_allocated': self._allocated } )

    @property
    def constraints(self):
        return self._constraints

    @constraints.setter
    def constraints(self, constraints):
        self._constraints = constraints

    def _get_size(self, index):
        ''' Calculates the size of a slice 
            :param index: a slice 
            :type index: slice
        '''
        size = index.stop - index.start
        if isinstance(size, BitVec):
            size = arithmetic_simplifier(size)
        else:
            size = BitVecConstant(self._address_size, size)
        assert isinstance(size, BitVecConstant)
        return size.value

    def __getitem__(self, index):
        if isinstance(index, slice):
            size = self._get_size(index)
            return self.read(index.start, size)
        else:
            return self.read(index, 1)[0]

    def __setitem__(self, index, value):
        if isinstance(index, slice):
            size = self._get_size(index)
            assert len(value) == size
            for i in xrange(size):
                self.write(index.start+i, [value[i]])
        else:
            self.write(index, [value])

    def __delitem__(self, index):
        def delete(offset):
            if offset in self.memory:
                del self._memory[offset]
            if offset in self._symbol:
                del self._symbols[offset]

        if isinstance(index, slice):
            for offset in xrange(index.start, index.end):
                delete(offset)
        else:
            delete(index)

    def __contains__(self, offset):
        return offset in self._memory or \
               offset in self._symbols

    def items(self):
        offsets = set( self._symbols.keys() + self._memory.keys())
        return [(x, self[x]) for x in offsets]

    def get(self, offset, default=0):
        result = self.read(offset, 1)
        if not result:
            return default
        return result[0]

    def __getitem__(self, index):
        if isinstance(index, slice):
            size = self._get_size(index)
            return self.read(index.start, size)
        else:
            return self.read(index, 1)[0]

    def __repr__(self):
        return self.__str__()

    def __str__(self):
        m = {}
        for key in self._memory.keys():
            c = self.read(key,1)[0]
            if issymbolic(c):
                m[key] = '?'
            else:
                m[key] = hex(c)
        return str(m)


    def __len__(self):
        return self._allocated

    @property
    def allocated(self):
        return self._allocated

    def _allocate(self, address):
        '''
            Allocate more memory
        '''
        new_max = ceil32(address) // 32
        self._allocated = Operators.ITEBV(256, self._allocated < new_max, new_max, self._allocated)

    def _concrete_read(self, address):
        return self._memory.get(address, 0)

    def _concrete_write(self, address, value):
        assert not issymbolic(address) 
        assert not issymbolic(value)
        assert value & ~(pow(2,self._value_size)-1) == 0 , "Not the correct size for a value"
        self._memory[address] = value

    def read(self, address, size):
        '''
        Read size items from address.
        Address can by a symbolic value.
        The result is a sequence the requested size.
        Resultant items can by symbolic.

        :param address: Where to read from
        :param size: How many items
        :rtype: list
        '''
        assert not issymbolic(size)
        self._allocate(address+size)

        if issymbolic(address):
            address = arithmetic_simplifier(address)
            assert solver.check(self.constraints)
            logger.debug('Reading %d items from symbolic offset %s', size, address)
            try:
                solutions = solver.get_all_values(self.constraints, address, maxcnt=0x1000) #if more than 0x3000 exception
            except TooManySolutions as e:
                m, M = solver.minmax(self.constraints, address)
                logger.debug('Got TooManySolutions on a symbolic read. Range [%x, %x]. Not crashing!', m, M)
                logger.info('INCOMPLETE Result! Using the sampled solutions we have as result')
                condition = False
                for base in e.solutions:
                    condition = Operators.OR(address == base, condition )
                raise ForkState('address too high', condition)

            #So here we have all potential solutions of symbolic address (complete set)
            assert len(solutions) > 0            

            condition = False
            for base in solutions:
                condition = Operators.OR(address == base, condition )

            result = []
            #consider size ==1 to read following code
            for offset in range(size):
                #Given ALL solutions for the symbolic address
                for base in solutions:
                    addr_value = base + offset
                    item = self._concrete_read(addr_value)
                    if addr_value in self._symbols:
                        for condition, value in self._symbols[addr_value]:
                            item = Operators.ITEBV(self._value_size, condition, value, item)
                    if len(result) > offset:
                        result[offset] = Operators.ITEBV(self._value_size, address == base, item, result[offset])
                    else:
                        result.append(item)
                    assert len(result) == offset+1
            return result
        else:
            result = []
            for i in range(size):
                result.append(self._concrete_read(address+i))
            for offset in range(size):
                if address+offset in self._symbols:
                    for condition, value in self._symbols[address+offset]:
                        if condition is True:
                            result[offset] = value
                        else:
                            result[offset] = Operators.ITEBV(self._value_size, condition, value, result[offset])
            return result

    def write(self, address, value):
        '''
        Write a value at address.
        :param address: The address at which to write
        :type address: int or long or Expression
        :param value: Bytes to write
        :type value: tuple or list
        '''
        size = len(value)
        self._allocate(address+size)

        if issymbolic(address):

            solutions = solver.get_all_values(self.constraints, address, maxcnt=0x1000) #if more than 0x3000 exception

            for offset in xrange(size):
                for base in solutions:
                    condition = base == address
                    self._symbols.setdefault(base+offset, []).append((condition, value[offset]))

        else:

            for offset in xrange(size):
                if issymbolic(value[offset]):
                    self._symbols[address+offset] = [(True, value[offset])]
                else:
                    # overwrite all previous items
                    if address+offset in self._symbols:
                        del self._symbols[address+offset]
                    self._concrete_write(address+offset, value[offset])
        
class EVMAsm(object):
    ''' 
        EVM Instruction factory
        
        Example use::

            >>> from manticore.platforms.evm import EVMAsm
            >>> EVMAsm.disassemble_one('\\x60\\x10')
            Instruction(0x60, 'PUSH', 1, 0, 1, 0, 'Place 1 byte item on stack.', 16, 0)
            >>> EVMAsm.assemble_one('PUSH1 0x10')
            Instruction(0x60, 'PUSH', 1, 0, 1, 0, 'Place 1 byte item on stack.', 16, 0)
            >>> tuple(EVMAsm.disassemble_all('\\x30\\x31'))
            (Instruction(0x30, 'ADDRESS', 0, 0, 1, 2, 'Get address of currently executing account.', None, 0), 
             Instruction(0x31, 'BALANCE', 0, 1, 1, 20, 'Get balance of the given account.', None, 1))
            >>> tuple(EVMAsm.assemble_all('ADDRESS\\nBALANCE'))
            (Instruction(0x30, 'ADDRESS', 0, 0, 1, 2, 'Get address of currently executing account.', None, 0),
             Instruction(0x31, 'BALANCE', 0, 1, 1, 20, 'Get balance of the given account.', None, 1))
            >>> EVMAsm.assemble_hex(
            ...                         """PUSH1 0x60
            ...                            BLOCKHASH 
            ...                            MSTORE
            ...                            PUSH1 0x2
            ...                            PUSH2 0x100
            ...                         """
            ...                      )
            '0x606040526002610100'
            >>> EVMAsm.disassemble_hex('0x606040526002610100')
            'PUSH1 0x60\\nBLOCKHASH\\nMSTORE\\nPUSH1 0x2\\nPUSH2 0x100'
    '''
    class Instruction(object):
        def __init__(self, opcode, name, operand_size, pops, pushes, fee, description, operand=None, offset=0):
            '''
            This represents an EVM instruction. 
            EVMAsm will create this for you.

            :param opcode: the opcode value
            :param name: instruction name
            :param operand_size: immediate operand size in bytes
            :param pops: number of items popped from the stack
            :param pushes: number of items pushed into the stack
            :param fee: gas fee for the instruction
            :param description: textual description of the instruction
            :param operand: optional immediate operand
            :param offset: optional offset of this instruction in the program

            Example use::

                instruction = EVMAsm.assemble_one('PUSH1 0x10')
                print 'Instruction: %s'% instruction
                print '\tdescription:', instruction.description
                print '\tgroup:', instruction.group
                print '\taddress:', instruction.offset
                print '\tsize:', instruction.size
                print '\thas_operand:', instruction.has_operand
                print '\toperand_size:', instruction.operand_size
                print '\toperand:', instruction.operand
                print '\tsemantics:', instruction.semantics
                print '\tpops:', instruction.pops
                print '\tpushes:', instruction.pushes
                print '\tbytes:', '0x'+instruction.bytes.encode('hex')
                print '\twrites to stack:', instruction.writes_to_stack
                print '\treads from stack:', instruction.reads_from_stack
                print '\twrites to memory:', instruction.writes_to_memory
                print '\treads from memory:', instruction.reads_from_memory
                print '\twrites to storage:', instruction.writes_to_storage
                print '\treads from storage:', instruction.reads_from_storage
                print '\tis terminator', instruction.is_terminator


            '''
            self._opcode = opcode 
            self._name = name 
            self._operand_size = operand_size
            self._pops = pops
            self._pushes = pushes
            self._fee = fee
            self._description = description
            self._operand = operand           #Immediate operand if any
            if operand_size != 0 and operand is not None:
                    mask = (1<<operand_size*8)-1
                    if ~mask & operand:
                        raise ValueError("operand should be %d bits long"%(operand_size*8))
            self._offset=offset

        def __eq__(self, other):
            ''' Instructions are equal if all features match '''
            return self._opcode == other._opcode and\
            self._name == other._name and\
            self._operand == other._operand and\
            self._operand_size == other._operand_size and\
            self._pops == other._pops and\
            self._pushes == other._pushes and\
            self._fee == other._fee and\
            self._offset == other._offset and\
            self._description == other._description 

        def __repr__(self):
            output = 'Instruction(0x%x, %r, %d, %d, %d, %d, %r, %r, %r)'%(self._opcode, self._name, self._operand_size, self._pops, self._pushes, self._fee, self._description, self._operand, self._offset)
            return output


        def __str__(self):
            output = self.name + (' 0x%x'%self.operand if self.has_operand else '')
            return output

        @property
        def opcode(self):
            ''' The opcode as an integer ''' 
            return self._opcode

        @property
        def name(self):
            ''' The instruction name/mnemonic ''' 
            if self._name == 'PUSH':
                return 'PUSH%d'%self.operand_size
            elif self._name == 'DUP':
                return 'DUP%d'%self.pops
            elif self._name == 'SWAP':
                return 'SWAP%d'%(self.pops-1)
            elif self._name == 'LOG':
                return 'LOG%d'%(self.pops-2)
            return self._name
            
        def parse_operand(self, buf):
            ''' Parses an operand from buf 

                :param buf: a buffer
                :type buf: iterator/generator/string
            '''
            buf = iter(buf)
            try:
                operand = 0
                for _ in range(self.operand_size):
                    operand <<= 8
                    operand |= ord(next(buf))
                self._operand = operand
            except StopIteration:
                raise Exception("Not enough data for decoding")

        @property
        def operand_size(self):
            ''' The immediate operand size '''
            return self._operand_size

        @property
        def has_operand(self):
            ''' True if the instruction uses an immediate operand'''
            return self.operand_size > 0

        @property
        def operand(self):
            ''' The immediate operand '''
            return self._operand

        @property
        def pops(self):
            '''Number words popped from the stack'''
            return self._pops

        @property
        def pushes(self):
            '''Number words pushed to the stack'''
            return self._pushes

        @property
        def size(self):
            ''' Size of the encoded instruction '''
            return self._operand_size + 1

        @property
        def fee(self):
            ''' The basic gas fee of the instruction '''
            return self._fee

        @property
        def semantics(self):
            ''' Canonical semantics '''
            return self._name

        @property
        def description(self):
            ''' Coloquial description of the instruction '''
            return self._description

        @property
        def bytes(self):
            ''' Encoded instruction '''
            bytes = []
            bytes.append(chr(self._opcode))
            for offset in reversed(xrange(self.operand_size)):
                c = (self.operand >> offset*8 ) & 0xff 
                bytes.append(chr(c))
            return ''.join(bytes)

        @property
        def offset(self):
            '''Location in the program (optional)'''
            return self._offset

        @property
        def group(self):
            '''Instruction classification as per the yellow paper'''
            classes = {
                        0:   'Stop and Arithmetic Operations',
                        1:   'Comparison & Bitwise Logic Operations',
                        2:   'SHA3',
                        3:   'Environmental Information',
                        4:   'Block Information',
                        5:   'Stack, Memory, Storage and Flow Operations',
                        6:   'Push Operations',
                        7:   'Push Operations',
                        8:   'Duplication Operations',
                        9:   'Exchange Operations',
                        0xa: 'Logging Operations',
                        0xf: 'System operations'
                      }
            return classes.get(self.opcode>>4, 'Invalid instruction')

        @property
        def uses_stack(self):
            ''' True if the instruction reads/writes from/to the stack '''
            return self.reads_from_stack or self.writes_to_stack

        @property
        def reads_from_stack(self):
            ''' True if the instruction reads from stack '''
            return self.pops > 0

        @property
        def writes_to_stack(self):
            ''' True if the instruction writes to the stack '''
            return self.pushes > 0
            
        @property
        def reads_from_memory(self):
            ''' True if the instruction reads from memory '''
            return self.semantics in ('MLOAD','CREATE', 'CALL', 'CALLCODE', 'RETURN', 'DELEGATECALL', 'REVERT')

        @property
        def writes_to_memory(self):
            ''' True if the instruction writes to memory '''
            return self.semantics in ('MSTORE', 'MSTORE8', 'CALLDATACOPY', 'CODECOPY', 'EXTCODECOPY')
            
        @property
        def reads_from_memory(self):
            ''' True if the instruction reads from memory '''
            return self.semantics in ('MLOAD','CREATE', 'CALL', 'CALLCODE', 'RETURN', 'DELEGATECALL', 'REVERT')

        @property
        def writes_to_storage(self):
            ''' True if the instruction writes to the storage '''
            return self.semantics in ('SSTORE')

        @property
        def reads_from_storage(self):
            ''' True if the instruction reads from the storage '''
            return self.semantics in ('SLOAD')

        @property
        def is_terminator(self):
            ''' True if the instruction is a basic block terminator '''
            return self.semantics in ('RETURN', 'STOP', 'INVALID', 'JUMP', 'JUMPI', 'SELFDESTRUCT', 'REVERT')

        @property
        def is_branch(self):
            ''' True if the instruction is a jump'''
            return self.semantics in ('JUMP', 'JUMPI')

        @property
        def is_environmental(self):
            ''' True if the instruction access enviromental data '''
            return self.group == 'Environmental Information'
            
        @property
        def is_system(self):
            ''' True if the instruction is a system operation '''
            return self.group == 'System operations'

        @property
        def uses_block_info(self):
            ''' True if the instruction access block information'''
            return self.group == 'Block Information'

        @property
        def is_arithmetic(self):
            ''' True if the instruction is an arithmetic operation '''
            return  self.semantics in ('ADD', 'MUL', 'SUB', 'DIV', 'SDIV', 'MOD', 'SMOD', 'ADDMOD', 'MULMOD', 'EXP', 'SIGNEXTEND')
 
    #from http://gavwood.com/paper.pdf
    _table = {#opcode: (name, immediate_operand_size, pops, pushes, gas, description)
                0x00: ('STOP', 0, 0, 0, 0, 'Halts execution.'),
                0x01: ('ADD', 0, 2, 1, 3, 'Addition operation.'),
                0x02: ('MUL', 0, 2, 1, 5, 'Multiplication operation.'),
                0x03: ('SUB', 0, 2, 1, 3, 'Subtraction operation.'),
                0x04: ('DIV', 0, 2, 1, 5, 'Integer division operation.'),
                0x05: ('SDIV', 0, 2, 1, 5, 'Signed integer division operation (truncated).'),
                0x06: ('MOD', 0, 2, 1, 5, 'Modulo remainder operation.'),
                0x07: ('SMOD', 0, 2, 1, 5, 'Signed modulo remainder operation.'),
                0x08: ('ADDMOD', 0, 3, 1, 8, 'Modulo addition operation.'),
                0x09: ('MULMOD', 0, 3, 1, 8, 'Modulo multiplication operation.'),
                0x0a: ('EXP', 0, 2, 1, 10, 'Exponential operation.'),
                0x0b: ('SIGNEXTEND', 0, 2, 1, 5, "Extend length of two's complement signed integer."),
                0x10: ('LT', 0, 2, 1, 3, 'Less-than comparision.'),
                0x11: ('GT', 0, 2, 1, 3, 'Greater-than comparision.'),
                0x12: ('SLT', 0, 2, 1, 3, 'Signed less-than comparision.'),
                0x13: ('SGT', 0, 2, 1, 3, 'Signed greater-than comparision.'),
                0x14: ('EQ', 0, 2, 1, 3, 'Equality comparision.'),
                0x15: ('ISZERO', 0, 1, 1, 3, 'Simple not operator.'),
                0x16: ('AND', 0, 2, 1, 3, 'Bitwise AND operation.'),
                0x17: ('OR', 0, 2, 1, 3, 'Bitwise OR operation.'),
                0x18: ('XOR', 0, 2, 1, 3, 'Bitwise XOR operation.'),
                0x19: ('NOT', 0, 1, 1, 3, 'Bitwise NOT operation.'),
                0x1a: ('BYTE', 0, 2, 1, 3, 'Retrieve single byte from word.'),
                0x20: ('SHA3', 0, 2, 1, 30, 'Compute Keccak-256 hash.'),
                0x30: ('ADDRESS', 0, 0, 1, 2, 'Get address of currently executing account     .'),
                0x31: ('BALANCE', 0, 1, 1, 20, 'Get balance of the given account.'),
                0x32: ('ORIGIN', 0, 0, 1, 2, 'Get execution origination address.'),
                0x33: ('CALLER', 0, 0, 1, 2, 'Get caller address.'),
                0x34: ('CALLVALUE', 0, 0, 1, 2, 'Get deposited value by the instruction/transaction responsible for this execution.'),
                0x35: ('CALLDATALOAD', 0, 1, 1, 3, 'Get input data of current environment.'),
                0x36: ('CALLDATASIZE', 0, 0, 1, 2, 'Get size of input data in current environment.'),
                0x37: ('CALLDATACOPY', 0, 3, 0, 3, 'Copy input data in current environment to memory.'),
                0x38: ('CODESIZE', 0, 0, 1, 2, 'Get size of code running in current environment.'),
                0x39: ('CODECOPY', 0, 3, 0, 3, 'Copy code running in current environment to memory.'),
                0x3a: ('GASPRICE', 0, 0, 1, 2, 'Get price of gas in current environment.'),
                0x3b: ('EXTCODESIZE', 0, 1, 1, 20, "Get size of an account's code."),
                0x3c: ('EXTCODECOPY', 0, 4, 0, 20, "Copy an account's code to memory."),
                0x40: ('BLOCKHASH', 0, 1, 1, 20, 'Get the hash of one of the 256 most recent complete blocks.'),
                0x41: ('COINBASE', 0, 0, 1, 2, "Get the block's beneficiary address."),
                0x42: ('TIMESTAMP', 0, 0, 1, 2, "Get the block's timestamp."),
                0x43: ('NUMBER', 0, 0, 1, 2, "Get the block's number."),
                0x44: ('DIFFICULTY', 0, 0, 1, 2, "Get the block's difficulty."),
                0x45: ('GASLIMIT', 0, 0, 1, 2, "Get the block's gas limit."),
                0x50: ('POP', 0, 1, 0, 2, 'Remove item from stack.'),
                0x51: ('MLOAD', 0, 1, 1, 3, 'Load word from memory.'),
                0x52: ('MSTORE', 0, 2, 0, 3, 'Save word to memory.'),
                0x53: ('MSTORE8', 0, 2, 0, 3, 'Save byte to memory.'),
                0x54: ('SLOAD', 0, 1, 1, 50, 'Load word from storage.'),
                0x55: ('SSTORE', 0, 2, 0, 0, 'Save word to storage.'),
                0x56: ('JUMP', 0, 1, 0, 8, 'Alter the program counter.'),
                0x57: ('JUMPI', 0, 2, 0, 10, 'Conditionally alter the program counter.'),
                0x58: ('GETPC', 0, 0, 1, 2, 'Get the value of the program counter prior to the increment.'),
                0x59: ('MSIZE', 0, 0, 1, 2, 'Get the size of active memory in bytes.'),
                0x5a: ('GAS', 0, 0, 1, 2, 'Get the amount of available gas, including the corresponding reduction the amount of available gas.'),
                0x5b: ('JUMPDEST', 0, 0, 0, 1, 'Mark a valid destination for jumps.'),
                0x60: ('PUSH', 1, 0, 1, 0, 'Place 1 byte item on stack.'),
                0x61: ('PUSH', 2, 0, 1, 0, 'Place 2-byte item on stack.'),
                0x62: ('PUSH', 3, 0, 1, 0, 'Place 3-byte item on stack.'),
                0x63: ('PUSH', 4, 0, 1, 0, 'Place 4-byte item on stack.'),
                0x64: ('PUSH', 5, 0, 1, 0, 'Place 5-byte item on stack.'),
                0x65: ('PUSH', 6, 0, 1, 0, 'Place 6-byte item on stack.'),
                0x66: ('PUSH', 7, 0, 1, 0, 'Place 7-byte item on stack.'),
                0x67: ('PUSH', 8, 0, 1, 0, 'Place 8-byte item on stack.'),
                0x68: ('PUSH', 9, 0, 1, 0, 'Place 9-byte item on stack.'),
                0x69: ('PUSH', 10, 0, 1, 0, 'Place 10-byte item on stack.'),
                0x6a: ('PUSH', 11, 0, 1, 0, 'Place 11-byte item on stack.'),
                0x6b: ('PUSH', 12, 0, 1, 0, 'Place 12-byte item on stack.'),
                0x6c: ('PUSH', 13, 0, 1, 0, 'Place 13-byte item on stack.'),
                0x6d: ('PUSH', 14, 0, 1, 0, 'Place 14-byte item on stack.'),
                0x6e: ('PUSH', 15, 0, 1, 0, 'Place 15-byte item on stack.'),
                0x6f: ('PUSH', 16, 0, 1, 0, 'Place 16-byte item on stack.'),
                0x70: ('PUSH', 17, 0, 1, 0, 'Place 17-byte item on stack.'),
                0x71: ('PUSH', 18, 0, 1, 0, 'Place 18-byte item on stack.'),
                0x72: ('PUSH', 19, 0, 1, 0, 'Place 19-byte item on stack.'),
                0x73: ('PUSH', 20, 0, 1, 0, 'Place 20-byte item on stack.'),
                0x74: ('PUSH', 21, 0, 1, 0, 'Place 21-byte item on stack.'),
                0x75: ('PUSH', 22, 0, 1, 0, 'Place 22-byte item on stack.'),
                0x76: ('PUSH', 23, 0, 1, 0, 'Place 23-byte item on stack.'),
                0x77: ('PUSH', 24, 0, 1, 0, 'Place 24-byte item on stack.'),
                0x78: ('PUSH', 25, 0, 1, 0, 'Place 25-byte item on stack.'),
                0x79: ('PUSH', 26, 0, 1, 0, 'Place 26-byte item on stack.'),
                0x7a: ('PUSH', 27, 0, 1, 0, 'Place 27-byte item on stack.'),
                0x7b: ('PUSH', 28, 0, 1, 0, 'Place 28-byte item on stack.'),
                0x7c: ('PUSH', 29, 0, 1, 0, 'Place 29-byte item on stack.'),
                0x7d: ('PUSH', 30, 0, 1, 0, 'Place 30-byte item on stack.'),
                0x7e: ('PUSH', 31, 0, 1, 0, 'Place 31-byte item on stack.'),
                0x7f: ('PUSH', 32, 0, 1, 0, 'Place 32-byte (full word) item on stack.'),
                0x80: ('DUP', 0, 1, 2, 3, 'Duplicate 1st stack item.'),
                0x81: ('DUP', 0, 2, 3, 3, 'Duplicate 2nd stack item.'),
                0x82: ('DUP', 0, 3, 4, 3, 'Duplicate 3rd stack item.'),
                0x83: ('DUP', 0, 4, 5, 3, 'Duplicate 4th stack item.'),
                0x84: ('DUP', 0, 5, 6, 3, 'Duplicate 5th stack item.'),
                0x85: ('DUP', 0, 6, 7, 3, 'Duplicate 6th stack item.'),
                0x86: ('DUP', 0, 7, 8, 3, 'Duplicate 7th stack item.'),
                0x87: ('DUP', 0, 8, 9, 3, 'Duplicate 8th stack item.'),
                0x88: ('DUP', 0, 9, 10, 3, 'Duplicate 9th stack item.'),
                0x89: ('DUP', 0, 10, 11, 3, 'Duplicate 10th stack item.'),
                0x8a: ('DUP', 0, 11, 12, 3, 'Duplicate 11th stack item.'),
                0x8b: ('DUP', 0, 12, 13, 3, 'Duplicate 12th stack item.'),
                0x8c: ('DUP', 0, 13, 14, 3, 'Duplicate 13th stack item.'),
                0x8d: ('DUP', 0, 14, 15, 3, 'Duplicate 14th stack item.'),
                0x8e: ('DUP', 0, 15, 16, 3, 'Duplicate 15th stack item.'),
                0x8f: ('DUP', 0, 16, 17, 3, 'Duplicate 16th stack item.'),
                0x90: ('SWAP', 0, 2, 2, 3, 'Exchange 1st and 2nd stack items.'),
                0x91: ('SWAP', 0, 3, 3, 3, 'Exchange 1st and 3rd stack items.'),
                0x92: ('SWAP', 0, 4, 4, 3, 'Exchange 1st and 4th stack items.'),
                0x93: ('SWAP', 0, 5, 5, 3, 'Exchange 1st and 5th stack items.'),
                0x94: ('SWAP', 0, 6, 6, 3, 'Exchange 1st and 6th stack items.'),
                0x95: ('SWAP', 0, 7, 7, 3, 'Exchange 1st and 7th stack items.'),
                0x96: ('SWAP', 0, 8, 8, 3, 'Exchange 1st and 8th stack items.'),
                0x97: ('SWAP', 0, 9, 9, 3, 'Exchange 1st and 9th stack items.'),
                0x98: ('SWAP', 0, 10, 10, 3, 'Exchange 1st and 10th stack items.'),
                0x99: ('SWAP', 0, 11, 11, 3, 'Exchange 1st and 11th stack items.'),
                0x9a: ('SWAP', 0, 12, 12, 3, 'Exchange 1st and 12th stack items.'),
                0x9b: ('SWAP', 0, 13, 13, 3, 'Exchange 1st and 13th stack items.'),
                0x9c: ('SWAP', 0, 14, 14, 3, 'Exchange 1st and 14th stack items.'),
                0x9d: ('SWAP', 0, 15, 15, 3, 'Exchange 1st and 15th stack items.'),
                0x9e: ('SWAP', 0, 16, 16, 3, 'Exchange 1st and 16th stack items.'),
                0x9f: ('SWAP', 0, 17, 17, 3, 'Exchange 1st and 17th stack items.'),
                0xa0: ('LOG', 0, 2, 0, 375, 'Append log record with no topics.'),
                0xa1: ('LOG', 0, 3, 0, 750, 'Append log record with one topic.'),
                0xa2: ('LOG', 0, 4, 0, 1125, 'Append log record with two topics.'),
                0xa3: ('LOG', 0, 5, 0, 1500, 'Append log record with three topics.'),
                0xa4: ('LOG', 0, 6, 0, 1875, 'Append log record with four topics.'),
                0xf0: ('CREATE', 0, 3, 1, 32000, 'Create a new account with associated code.'),
                0xf1: ('CALL', 0, 7, 1, 40, 'Message-call into an account.'),
                0xf2: ('CALLCODE', 0, 7, 1, 40, "Message-call into this account with alternative account's code."),
                0xf3: ('RETURN', 0, 2, 0, 0, 'Halt execution returning output data.'),
                0xf4: ('DELEGATECALL', 0, 6, 1, 40, "Message-call into this account with an alternative account's code, but persisting into this account with an alternative account's code."),
                0xf5: ('BREAKPOINT', 0, 0, 0, 40, 'Not in yellow paper FIXME'),
                0xf6: ('RNGSEED', 0, 1, 1, 0, 'Not in yellow paper FIXME'),
                0xf7: ('SSIZEEXT', 0, 2, 1, 0, 'Not in yellow paper FIXME'),
                0xf8: ('SLOADBYTES', 0, 3, 0, 0, 'Not in yellow paper FIXME'),
                0xf9: ('SSTOREBYTES', 0, 3, 0, 0, 'Not in yellow paper FIXME'),
                0xfa: ('SSIZE', 0, 1, 1, 40, 'Not in yellow paper FIXME'),
                0xfb: ('STATEROOT', 0, 1, 1, 0, 'Not in yellow paper FIXME'),
                0xfc: ('TXEXECGAS', 0, 0, 1, 0, 'Not in yellow paper FIXME'),
                0xfd: ('REVERT', 0, 2, 0, 0, 'Stop execution and revert state changes, without consuming all provided gas and providing a reason.'),
                0xfe: ('INVALID', 0, 0, 0, 0, 'Designated invalid instruction.'),
                0xff: ('SELFDESTRUCT', 0, 1, 0, 5000, 'Halt execution and register account for later deletion.')
            }

    @staticmethod
    @memoized
    def _get_reverse_table():
        ''' Build an internal table used in the assembler '''
        reverse_table = {}
        for (opcode, (name, immediate_operand_size, pops, pushes, gas, description)) in EVMAsm._table.items():
            mnemonic = name
            if name == 'PUSH':
                mnemonic = '%s%d'%(name, (opcode&0x1f) + 1)
            elif name in ('SWAP', 'LOG', 'DUP'):
                mnemonic = '%s%d'%(name, (opcode&0xf) + 1)

            reverse_table[mnemonic] = opcode, name, immediate_operand_size, pops, pushes, gas, description
        return reverse_table

    @staticmethod
    def assemble_one(assembler, offset=0):
        ''' Assemble one EVM instruction from its textual representation. 
            
            :param assembler: assembler code for one instruction
            :param offset: offset of the instruction in the bytecode (optional)
            :return: An Instruction object

            Example use::

                >>> print evm.EVMAsm.assemble_one('LT')
            

        '''
        try:
            _reverse_table = EVMAsm._get_reverse_table()
            assembler = assembler.strip().split(' ')
            opcode, name, operand_size, pops, pushes, gas, description = _reverse_table[assembler[0].upper()]
            if operand_size > 0:
                assert len(assembler) == 2
                operand = int(assembler[1],0)
            else:
                assert len(assembler) == 1
                operand = None

            return EVMAsm.Instruction(opcode, name, operand_size, pops, pushes, gas, description, operand=operand, offset=offset)
        except:
            raise Exception("Something wrong at offset %d"%offset)

    @staticmethod
    def assemble_all(assembler, offset=0):
        ''' Assemble a sequence of textual representation of EVM instructions 

            :param assembler: assembler code for any number of instructions
            :param offset: offset of the first instruction in the bytecode(optional)
            :return: An generator of Instruction objects

            Example use::
            
                >>> evm.EVMAsm.encode_one("""PUSH1 0x60
                    PUSH1 0x40
                    MSTORE
                    PUSH1 0x2
                    PUSH2 0x108
                    PUSH1 0x0
                    POP
                    SSTORE
                    PUSH1 0x40
                    MLOAD
                    """)

        '''
        if isinstance(assembler, str):
            assembler = assembler.split('\n')
        assembler = iter(assembler)
        for line in assembler:
            if not line.strip():
                continue
            instr = EVMAsm.assemble_one(line, offset=offset)
            yield instr
            offset += instr.size

    @staticmethod
    def disassemble_one(bytecode, offset=0):
        ''' Decode a single instruction from a bytecode

            :param bytecode: the bytecode stream 
            :param offset: offset of the instruction in the bytecode(optional)
            :type bytecode: iterator/sequence/str
            :return: an Instruction object

            Example use::
            
                >>> print EVMAsm.assemble_one('PUSH1 0x10')

        '''
        bytecode = iter(bytecode)
        opcode = ord(next(bytecode))
        invalid = ('INVALID', 0, 0, 0, 0, 'Unknown opcode')
        name, operand_size, pops, pushes, gas, description = EVMAsm._table.get(opcode, invalid)
        instruction = EVMAsm.Instruction(opcode, name, operand_size, pops, pushes, gas, description, offset=offset)
        if instruction.has_operand:
            instruction.parse_operand(bytecode)

        return instruction

    @staticmethod
    def disassemble_all(bytecode, offset=0):
        ''' Decode all instructions in bytecode

            :param bytecode: an evm bytecode (binary)
            :param offset: offset of the first instruction in the bytecode(optional)
            :type bytecode: iterator/sequence/str
            :return: An generator of Instruction objects

            Example use::
            
                >>> for inst in EVMAsm.decode_all(bytecode):
                ...    print inst

                ... 
                PUSH1 0x60
                PUSH1 0x40
                MSTORE
                PUSH1 0x2
                PUSH2 0x108
                PUSH1 0x0
                POP
                SSTORE
                PUSH1 0x40
                MLOAD


        '''

        bytecode = iter(bytecode)
        while True:
            instr = EVMAsm.disassemble_one(bytecode, offset=offset)
            offset += instr.size
            yield instr

    @staticmethod
    def disassemble(bytecode, offset=0):
        ''' Disassemble an EVM bytecode 

            :param bytecode: binary representation of an evm bytecode (hexadecimal)
            :param offset: offset of the first instruction in the bytecode(optional)
            :type bytecode: str
            :return: the text representation of the aseembler code

            Example use::
            
                >>> EVMAsm.disassemble("\x60\x60\x60\x40\x52\x60\x02\x61\x01\x00")
                ...
                PUSH1 0x60
                BLOCKHASH
                MSTORE
                PUSH1 0x2
                PUSH2 0x100

        '''
        return '\n'.join(map(str, EVMAsm.disassemble_all(bytecode, offset=offset)))

    @staticmethod
    def assemble(asmcode, offset=0):
        ''' Assemble an EVM program 

            :param asmcode: an evm assembler program
            :param offset: offset of the first instruction in the bytecode(optional)
            :type asmcode: str
            :return: the hex representation of the bytecode

            Example use::
            
                >>> EVMAsm.assemble(  """PUSH1 0x60
                                           BLOCKHASH
                                           MSTORE
                                           PUSH1 0x2
                                           PUSH2 0x100
                                        """
                                     )
                ...
                "\x60\x60\x60\x40\x52\x60\x02\x61\x01\x00"
        '''
        return ''.join(map(lambda x:x.bytes, EVMAsm.assemble_all(asmcode, offset=offset)))

    @staticmethod
    def disassemble_hex(bytecode, offset=0):
        ''' Disassemble an EVM bytecode 

            :param bytecode: canonical representation of an evm bytecode (hexadecimal)
            :param int offset: offset of the first instruction in the bytecode(optional)
            :type bytecode: str
            :return: the text representation of the aseembler code

            Example use::
            
                >>> EVMAsm.disassemble_hex("0x6060604052600261010")
                ...
                PUSH1 0x60
                BLOCKHASH
                MSTORE
                PUSH1 0x2
                PUSH2 0x100

        '''
        if bytecode.startswith('0x'):
            bytecode = bytecode[2:]
        bytecode = bytecode.decode('hex')
        return EVMAsm.disassemble(bytecode, offset=offset)

    @staticmethod
    def assemble_hex(asmcode, offset=0):
        ''' Assemble an EVM program 

            :param asmcode: an evm assembler program
            :param offset: offset of the first instruction in the bytecode(optional)
            :type asmcode: str
            :return: the hex representation of the bytecode

            Example use::
            
                >>> EVMAsm.assemble_hex(  """PUSH1 0x60
                                           BLOCKHASH
                                           MSTORE
                                           PUSH1 0x2
                                           PUSH2 0x100
                                        """
                                     )
                ...
                "0x6060604052600261010"
        '''
        return '0x' + EVMAsm.assemble(asmcode, offset=offset).encode('hex')



#Exceptions...

class EVMException(Exception):
    pass

class EVMInstructionException(EVMException):
    pass

class ConcretizeStack(EVMException):
    '''
    Raised when a symbolic memory cell needs to be concretized.
    '''
    def __init__(self, pos, expression=None, policy='MINMAX'):
        self.message = "Concretizing evm stack item {}".format(pos)
        self.pos = pos
        self.expression = expression
        self.policy = policy

class StackOverflow(EVMException):
    ''' Attemped to push more than 1024 items '''
    pass

class StackUnderflow(EVMException):
    ''' Attemped to popo from an empty stack '''
    pass

class InvalidOpcode(EVMException):
    ''' Trying to execute invalid opcode '''
    pass


class Call(EVMInstructionException):
    def __init__(self, gas, to, value, data, out_offset=None, out_size=None):
        self.gas = gas
        self.to = to
        self.value = value
        self.data = data
        self.out_offset = out_offset
        self.out_size = out_size

    def __reduce__(self):
        return (self.__class__, (self.gas, self.to, self.value, self.data, self.out_offset, self.out_size) )

class Create(Call):
    def __init__(self, value, offset, size):
        super(Create, self).__init__(gas=None, to=None, value=value, data='')

class DelegateCall(Call):
    pass

class Stop(EVMInstructionException):
    ''' Program reached a STOP instruction '''
    pass

class Return(EVMInstructionException):
    ''' Program reached a RETURN instruction '''
    def __init__(self, data):
        self.data = data
    def __reduce__(self):
        return (self.__class__, (self.data,) )

class Revert(EVMInstructionException):
    ''' Program reached a RETURN instruction '''
    def __init__(self, data):
        self.data = data
    def __reduce__(self):
        return (self.__class__, (self.data,) )

class SelfDestruct(EVMInstructionException):
    ''' Program reached a RETURN instruction '''
    def __init__(self, to):
        self.to = to

class NotEnoughGas(EVMException):
    ''' Not enough gas for operation '''
    pass

class Sha3(EVMException):
    def __init__(self, data):
        self.data = data

    def __reduce__(self):
        return (self.__class__, (self.data, ))


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
    def __init__(self, constraints, address, origin, price, data, caller, value, code, header, global_storage=None, depth=0, gas=1000000000, **kwargs):
        '''
        Builds a Ethereum Virtual Machine instance

        :param memory: the initial memory
        :param address: the address of the account which owns the code that is executing.
        :param origin: the sender address of the transaction that originated this execution. A 160-bit code used for identifying Accounts.
        :param price: the price of gas in the transaction that originated this execution.
        :param data: the byte array that is the input data to this execution
        :param caller: the address of the account which caused the code to be executing. A 160-bit code used for identifying Accounts
        :param value: the value, in Wei, passed to this account as part of the same procedure as execution. One Ether is defined as being 10**18 Wei.
        :param bytecode: the byte array that is the machine code to be executed.
        :param header: the block header of the present block.
        :param depth: the depth of the present message-call or contract-creation (i.e. the number of CALLs or CREATEs being executed at present).

        '''
        super(EVM, self).__init__(**kwargs)
        self._constraints = constraints
        self.last_exception = None
        self.memory = EVMMemory(constraints)
        self.address = address
        self.origin = origin # always an account with empty associated code
        self.caller = caller # address of the account that is directly responsible for this execution
        self.data = data
        self.price = price #This is gas price specified by the originating transaction
        self.value = value
        self.depth = depth
        self.bytecode = code
        self.suicides = set()
        self.logs = []
        self.gas=gas
        #FIXME parse decode and mark invalid instructions
        #self.invalid = set()

        assert 'coinbase' in header
        assert 'gaslimit' in header
        assert 'difficulty' in header
        assert 'timestamp' in header
        assert 'number' in header
        self.header=header

        #Machine state
        self.pc = 0
        self.stack = []
        self.gas = gas
        self.global_storage = global_storage
        self.allocated = 0

    @property
    def constraints(self):
        return self._constraints

    @constraints.setter
    def constraints(self, constraints):
        self._constraints = constraints
        self.memory.constraints = constraints


    def __getstate__(self):
        state = super(EVM, self).__getstate__()
        state['gas'] = self.gas
        state['memory'] = self.memory
        state['global_storage'] = self.global_storage
        state['constraints'] = self.constraints
        state['last_exception'] = self.last_exception
        state['address'] = self.address
        state['origin'] = self.origin
        state['caller'] = self.caller
        state['data'] = self.data
        state['price'] = self.price
        state['value'] = self.value
        state['depth'] = self.depth
        state['bytecode'] = self.bytecode
        state['header'] = self.header
        state['pc'] = self.pc
        state['stack'] = self.stack
        state['gas'] = self.gas
        state['allocated'] = self.allocated
        state['suicides'] = self.suicides
        state['logs'] = self.logs

        return state

    def __setstate__(self, state):
        self.gas = state['gas']
        self.memory = state['memory']
        self.logs = state['logs'] 
        self.global_storage = state['global_storage']
        self.constraints = state['constraints']
        self.last_exception = state['last_exception']
        self.address = state['address']
        self.origin = state['origin']
        self.caller = state['caller']
        self.data = state['data']
        self.price = state['price']
        self.value = state['value']
        self.depth = state['depth']
        self.bytecode = state['bytecode']
        self.header = state['header']
        self.pc = state['pc']
        self.stack = state['stack']
        self.gas = state['gas']
        self.allocated = state['allocated']
        self.suicides = state['suicides']
        super(EVM, self).__setstate__(state)

    #Memory related
    def _allocate(self, address):
        if address > self.memory._allocated:
            GMEMORY = 3
            GQUADRATICMEMDENOM = 512  # 1 gas per 512 quadwords

            old_size = ceil32(self.memory._allocated) // 32
            old_totalfee = old_size * GMEMORY + old_size ** 2 // GQUADRATICMEMDENOM
            new_size = ceil32(address) // 32
            increased = new_size - old_size 
            fee = increased * GMEMORY + increased**2 // GQUADRATICMEMDENOM
            self._consume(fee)

    def _store(self, address, value):
        #CHECK ADDRESS IS A 256 BIT INT OR BITVEC
        #CHECK VALUE IS A 256 BIT INT OR BITVEC
        self._allocate(address)
        self.memory.write(address, [value])
        self._publish('did_evm_write_memory', address, value)


    def _load(self, address):
        self._allocate(address)
        value = self.memory.read(address,1)[0]
        value = arithmetic_simplifier(value)
        if isinstance(value, Constant) and not value.taint: 
            value = value.value
        self._publish('did_evm_read_memory', address, value)

        return value

    @staticmethod
    def check256int(value):
        assert True

    def read_code(self, address, size=1):
        '''
            Read size byte from bytecode.
            If less than size bytes are available result will be pad with \x00
        '''
        assert address < len(self.bytecode)
        value = self.bytecode[address:address+size]
        if len(value) < size:
            value += '\x00'* (size-len(value)) #pad with null (spec)
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
        #FIXME check if pc points to invalid instruction
        #if self.pc >= len(self.bytecode):
        #    return InvalidOpcode('Code out of range')
        #if self.pc in self.invalid:
        #    raise InvalidOpcode('Opcode inside a PUSH immediate')

        def getcode():
            for byte in self.bytecode[self.pc:]:
                yield byte
            while True:
                yield '\x00'

        return EVMAsm.disassemble_one(getcode())

    #auxiliar funcs
    #Stack related
    def _push(self, value):
        '''
                   ITEM0
                   ITEM1
                   ITEM2
             sp->  {empty}
        '''
        assert isinstance(value,(int,long)) or isinstance(value, BitVec) and value.size==256 
        if len(self.stack) >= 1024:
            raise StackOverflow()
        self.stack.append(value & TT256M1)

    def _pop(self):
        if len(self.stack) == 0:
            raise StackUnderflow()
        return self.stack.pop()

    def _consume(self, fee):
        assert fee>=0
        if self.gas < fee:
            raise NotEnoughGas()
        self.gas -= fee

    #Execute an instruction from current pc
    def execute(self):
        if issymbolic(self.pc):
            expression = self.pc
            def setstate(state, value):
                state.platform.current.pc = value

            raise Concretize("Concretice PC",
                                expression=expression, 
                                setstate=setstate,
                                policy='ALL')

        self._publish('will_decode_instruction', self.pc)
        last_pc = self.pc
        current = self.instruction

        #Consume some gas
        self._consume(current.fee)

        implementation = getattr(self, current.semantics, None)
        if implementation is None:
            raise TerminateState("Instruction not implemented %s"%current.semantics, testcase=True)

        #Get arguments (imm, pop)
        arguments = []
        if self.instruction.has_operand:
            arguments.append(current.operand)

        for _ in range(current.pops):
            arguments.append(self._pop())

        #simplify stack arguments
        for i in range(len(arguments)):
            if isinstance(arguments[i], Expression):           
                arguments[i] = arithmetic_simplifier(arguments[i])
            if isinstance(arguments[i], Constant):
                arguments[i] = arguments[i].value

        self._publish('will_execute_instruction', self.pc, current)
        self._publish('will_evm_execute_instruction', current, arguments)

        last_pc = self.pc
        result = None

        try:
            result = implementation(*arguments)
            self._emit_did_execute_signals(current, arguments, result, last_pc)
        except ConcretizeStack as ex:
            for arg in reversed(arguments):
                self._push(arg)
            def setstate(state, value):
                self.stack[-ex.pos] = value
            raise Concretize("Concretice Stack Variable",
                                expression=self.stack[-ex.pos], 
                                setstate=setstate,
                                policy=ex.policy)
        except EVMException as e:
            self.last_exception = e

            # Technically, this is not the right place to emit these events because the
            # instruction hasn't executed yet; it executes in the EVM platform class (EVMWorld).
            # However, when I tried that, in the event handlers, `state.platform.current`
            # ends up being None, which caused issues. So, as a pragmatic solution, we emit
            # the event before technically executing the instruction.
            if isinstance(e, EVMInstructionException):
                self._emit_did_execute_signals(current, arguments, result, last_pc)

            raise

        #Check result (push)
        if current.pushes > 1:
            assert len(result) == current.pushes
            for value in reversed(result):
                self._push(value)
        elif current.pushes == 1:
            self._push(result)
        else:
            assert current.pushes == 0
            assert result is None
        if current.semantics not in ('JUMP', 'JUMPI'):
            #advance pc pointer
            self.pc += self.instruction.size

    def _emit_did_execute_signals(self, current, arguments, result, last_pc):
        self._publish('did_evm_execute_instruction', current, arguments, result)
        self._publish('did_execute_instruction', last_pc, self.pc, current)

    #INSTRUCTIONS
    def INVALID(self):
        '''Halts execution'''
        raise InvalidOpcode()

    ##########################################################################
    ## Stop and Arithmetic Operations
    ##  All arithmetic is modulo 256 unless otherwise noted. 

    def STOP(self):
        ''' Halts execution '''
        raise Stop()

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
        return Operators.ITEBV(256, b==0, 0, result)

    def SDIV(self, a, b):
        '''Signed integer division operation (truncated)'''        
        s0, s1 = to_signed(a), to_signed(b)
        try:
            result = (abs(s0) // abs(s1) * (-1 if s0 * s1 < 0 else 1))
        except ZeroDivisionError:
            result = 0
        return Operators.ITEBV(256, b == 0, 0, result)

    def MOD(self, a,b):
        '''Modulo remainder operation'''
        try:
            result = Operators.ITEBV(256, b==0, 0, a%b)
        except ZeroDivisionError:
            result = 0
        return result

    def SMOD(self, a, b):
        '''Signed modulo remainder operation'''
        s0, s1 = to_signed(a), to_signed(b)
        sign = Operators.ITEBV(256,  s0 < 0, -1, 1)
        try:
            result =  abs(s0) % abs(s1) * sign 
        except ZeroDivisionError:
            result = 0

        return Operators.ITEBV(256, s1==0, 0, result) 

    def ADDMOD(self, a, b, c):
        '''Modulo addition operation'''
        try:
            result = Operators.ITEBV(256, c==0, 0, (a+b)%c)
        except ZeroDivisionError:
            result = 0
        return result 

    def MULMOD(self, a, b, c):
        '''Modulo addition operation'''
        try:
            result = Operators.ITEBV(256, c==0, 0, (a*b)%c)
        except ZeroDivisionError:
            result = 0
        return result 


    def EXP(self, base, exponent):
        '''
            Exponential operation
            The zero-th power of zero 0^0 is defined to be one
        '''
        #fixme integer bitvec
        EXP_SUPPLEMENTAL_GAS = 50   # cost of EXP exponent per byte        
        def nbytes(e):
            for i in range(32):
                if e>>(i*8) == 0:
                    return i
            return 32
        self._consume(EXP_SUPPLEMENTAL_GAS * nbytes(exponent))
        return pow(base, exponent, TT256)

    def SIGNEXTEND(self, size, value): 
        '''Extend length of two's complement signed integer'''
        #FIXME maybe use Operators.SEXTEND
        testbit = Operators.ITEBV(256, size<=31, size * 8 +7, 257)
        result1 = (value | (TT256 - (1 << testbit)))
        result2 = (value & ((1 << testbit) - 1))
        result = Operators.ITEBV(256, (value & (1 << testbit)) != 0, result1, result2)
        return Operators.ITEBV(256, size<=31, result, value)

    ##########################################################################
    ##Comparison & Bitwise Logic Operations
    def LT(self, a, b): 
        '''Less-than comparision'''
        return Operators.ITEBV(256, Operators.ULT(a, b), 1, 0)

    def GT(self, a, b):
        '''Greater-than comparision'''
        return Operators.ITEBV(256, Operators.UGT(a, b), 1, 0)

    def SLT(self, a, b): 
        '''Signed less-than comparision'''
        #http://gavwood.com/paper.pdf
        s0, s1 = to_signed(a), to_signed(b)
        return Operators.ITEBV(256, s0 < s1, 1, 0)

    def SGT(self, a, b):
        '''Signed greater-than comparision'''
        #http://gavwood.com/paper.pdf
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
        offset = Operators.ITEBV(256, offset<32, (31-offset)*8, 256) 
        return Operators.ZEXTEND(Operators.EXTRACT(value, offset, 8), 256)


    def SHA3(self, start, size):
        '''Compute Keccak-256 hash'''
        GSHA3WORD = 6         # Cost of SHA3 per word
        #read memory from start to end
        #calculate hash on it/ maybe remember in some structure where that hash came from
        #http://gavwood.com/paper.pdf
        if size:
            self._consume(GSHA3WORD * (ceil32(size) // 32) )
        data = self.read_buffer(start, size)
        if any(map(issymbolic, data)):
            raise Sha3(data)

        buf = ''.join(data)
        value = sha3.keccak_256(buf).hexdigest()
        value = int('0x'+value,0)
        self._publish('on_concrete_sha3', buf, value)
        logger.info("Found a concrete SHA3 example %r -> %x", buf, value)
        return value



    ##########################################################################
    ##Environmental Information
    def ADDRESS(self): 
        '''Get address of currently executing account     '''
        return self.address

    def BALANCE(self, account):
        '''Get balance of the given account'''
        BALANCE_SUPPLEMENTAL_GAS = 380
        self._consume(BALANCE_SUPPLEMENTAL_GAS)
        if account & TT256M1 not in self.global_storage:
            return 0
        value = self.global_storage[account & TT256M1 ]['balance']
        if value is None:
            return 0
        return value

    def ORIGIN(self): 
        '''Get execution origination address'''
        return self.origin

    def CALLER(self): 
        '''Get caller address'''
        return Operators.ZEXTEND(self.caller, 256)

    def CALLVALUE(self):
        '''Get deposited value by the instruction/transaction responsible for this execution'''
        return self.value

    def CALLDATALOAD(self, offset):
        '''Get input data of current environment'''
        #FIXME concretize offset?
        #if issymbolic(offset):
        #    self._constraints.add(Operators.ULE(offset, len(self.data)+32))
            #self._constraints.add(0 == offset%32)
        #    raise ConcretizeStack(3, expression=offset, policy='ALL')

        bytes = list(self.data[offset:offset+32])
        bytes += list('\x00'*( 32-len(bytes)))
        bytes = map(Operators.ORD, bytes)
        value = Operators.CONCAT(256, *bytes)
        return value 

    def CALLDATASIZE(self):
        '''Get size of input data in current environment'''
        return len(self.data)

    def CALLDATACOPY(self, mem_offset, data_offset, size):
        '''Copy input data in current environment to memory'''
        GCOPY = 3             # cost to copy one 32 byte word
        self._consume(GCOPY * ceil32(size) // 32)


        #FIXME put zero if not enough data
        if issymbolic(size) or issymbolic(data_offset):
            #self._constraints.add(Operators.ULE(data_offset, len(self.data)))
            self._constraints.add(Operators.ULE(size+data_offset, len(self.data) + (32-len(self.data)%32) ))

        if issymbolic(size):
            raise ConcretizeStack(3, policy='ALL')

        for i in range(size):
            c = Operators.ITEBV(8,data_offset+i < len(self.data), Operators.ORD(self.data[data_offset+i]), 0)
            self._store(mem_offset+i, c)

    def CODESIZE(self):
        '''Get size of code running in current environment'''
        return len(self.bytecode)

    def CODECOPY(self, mem_offset, code_offset, size):
        '''Copy code running in current environment to memory'''
        if issymbolic(size):
            raise ConcretizeStack(3)
        GCOPY = 3             # cost to copy one 32 byte word
        self._consume(GCOPY * ceil32(size) // 32)

        for i in range(size):
            if (code_offset+i > len(self.bytecode)):
                self._store(mem_offset+i, 0)
            else:
                self._store(mem_offset+i, Operators.ORD(self.bytecode[code_offset+i]))
        self._publish( 'did_evm_read_code', code_offset, size)

    def GASPRICE(self):
        '''Get price of gas in current environment'''
        return self.price

    def EXTCODESIZE(self, account):
        '''Get size of an account's code'''
        #FIXME
        if not account & TT256M1 in self.global_storage:
            return 0
        return len(self.global_storage[account & TT256M1]['code'])

    def EXTCODECOPY(self, account, address, offset, size): 
        '''Copy an account's code to memory'''
        #FIXME STOP! if not enough data
        if not account & TT256M1 in self.global_storage:
            return
        extbytecode = self.global_storage[account& TT256M1]['code']
        GCOPY = 3             # cost to copy one 32 byte word
        self._consume(GCOPY * ceil32(len(extbytecode)) // 32)

        for i in range(size):
            if offset + i < len(extbytecode):
                self._store(address+i, extbytecode[offset+i])
            else:
                self._store(address+i, 0)

    ##########################################################################
    ##Block Information
    def BLOCKHASH(self, a):
        '''Get the hash of one of the 256 most recent complete blocks'''

        # We are not maintaining an actual -block-chain- so we just generate 
        # some hashes for each virtual block
        value = sha3.keccak_256(repr(a)+'NONCE').hexdigest()
        value = int('0x'+value,0)

        # 0 is left on the stack if the looked for block number is greater than the current block number
        # or more than 256 blocks behind the current block.
        value = Operators.ITEBV(256, Operators.OR( a > self.header['number'], a < max(0, self.header['number']-256)), 0 , value)
        return value

    def COINBASE(self):
        '''Get the block's beneficiary address'''
        return self.header['coinbase']

    def TIMESTAMP(self):
        '''Get the block's timestamp'''
        return self.header['timestamp']

    def NUMBER(self):
        '''Get the block's number'''
        return self.header['number']

    def DIFFICULTY(self):
        '''Get the block's difficulty'''
        return self.header['difficulty']

    def GASLIMIT(self):
        '''Get the block's gas limit'''
        return self.header['gaslimit']

    ##########################################################################
    ##Stack, Memory, Storage and Flow Operations
    def POP(self, a):
        '''Remove item from stack'''
        #Items are automatically removed from stack 
        #by the instruction distpatcher
        pass

    def MLOAD(self, address):
        '''Load word from memory'''
        bytes = []
        for offset in xrange(32):
            bytes.append(self._load(address+offset))
        return Operators.CONCAT(256, *bytes)

    def MSTORE(self, address, value):
        '''Save word to memory'''
        for offset in xrange(32):
            self._store(address+offset, Operators.EXTRACT(value, (31-offset)*8, 8))

    def MSTORE8(self, address, value):
        '''Save byte to memory'''
        self._store(address, Operators.EXTRACT(value, 0, 8))

    def SLOAD(self, offset):
        '''Load word from storage'''
        self._publish('will_evm_read_storage', offset)
        value = self.global_storage[self.address]['storage'].get(offset,0)
        self._publish('did_evm_read_storage', offset, value)
        return value

    def SSTORE(self, offset, value):
        '''Save word to storage'''
        self._publish('will_evm_write_storage', offset, value)
        self.global_storage[self.address]['storage'][offset] = value
        if value is 0:
            del self.global_storage[self.address]['storage'][offset]
        self._publish('did_evm_write_storage', offset, value)

    def JUMP(self, dest):
        '''Alter the program counter'''
        self.pc = dest
        #TODO check for JUMPDEST on next iter?
    
    def JUMPI(self, dest, cond):
        '''Conditionally alter the program counter'''
        self.pc = Operators.ITEBV(256, cond!=0, dest, self.pc + self.instruction.size)
        assert self.bytecode[dest] == '\x5b', "Must be jmpdest instruction" #fixme what if dest == self.pc + self.instruction.size?

    def GETPC(self):
        '''Get the value of the program counter prior to the increment'''
        return self.pc

    def MSIZE(self):
        '''Get the size of active memory in bytes'''
        return self.memory._allocated * 32

    def GAS(self):
        '''Get the amount of available gas, including the corresponding reduction the amount of available gas'''
        #fixme calculate gas consumption
        return self.gas

    def JUMPDEST(self):
        '''Mark a valid destination for jumps'''
        pass

    ##########################################################################
    ##Push Operations
    def PUSH(self, value):
        '''Place 1 to 32 bytes item on stack'''
        return value

    ##########################################################################
    ##Duplication Operations
    def DUP(self, *operands):
        '''Duplicate stack item'''
        return (operands[-1],) + operands

    ##########################################################################
    ##Exchange Operations
    def SWAP(self, *operands):
        '''Exchange 1st and 2nd stack items'''
        a = operands[0] 
        b = operands[-1]
        return (b,) + operands[1:-1] + (a,)

    ##########################################################################
    ##Logging Operations
    def LOG(self, address, size, *topics):

        if issymbolic(size):
            raise ConcretizeStack(2, policy='ONE')

        memlog = self.read_buffer(address, size)

        self.logs.append(EVMLog(self.address, memlog, topics))
        logger.info('LOG %r %r', memlog, topics)

    ##########################################################################
    ##System operations
    def read_buffer(self, offset, size):
        if size:
            self._allocate(offset+size)

        data = []
        for i in xrange(size):
            data.append(Operators.CHR(self._load(offset+i)))

        if any(map(issymbolic, data)):
            data_symb = self._constraints.new_array(index_bits=256, index_max=len(data))
            for i in range(len(data)):
                data_symb[i] = Operators.ORD(data[i])
            data = data_symb
        else:
            data = ''.join(data)

        return data

    def write_buffer(self, offset, buf):
        count = 0
        for c in buf:
            self._store(offset+count, c)
            count +=1 

    def CREATE(self, value, offset, size):
        '''Create a new account with associated code'''
        code = self.read_buffer(offset, size)
        raise Create(value, code)

    def CALL(self, gas, to, value, in_offset, in_size, out_offset, out_size):
        '''Message-call into an account'''
        if issymbolic(in_offset):
            raise ConcretizeStack(4, policy='SAMPLED')
        if issymbolic(in_size):
            raise ConcretizeStack(5, policy='SAMPLED')

        data = self.read_buffer(in_offset, in_size)
        raise Call(gas, to, value, data, out_offset, out_size)

    def CALLCODE(self, gas, to, value, in_offset, in_size, out_offset, out_size):
        '''Message-call into this account with alternative account's code'''
        data = self.read_buffer(in_offset, in_size)
        raise Call(gas, self.address, value, data, out_offset, out_size)

    def RETURN(self, offset, size):
        '''Halt execution returning output data'''
        data = self.read_buffer(offset, size)
        raise Return(data)

    def DELEGATECALL(self, gas, to, in_offset, in_size, out_offset, out_size):
        '''Message-call into this account with an alternative account's code, but persisting into this account with an alternative account's code'''
        value = 0
        data = self.read_buffer(in_offset, in_size)
        raise Call(gas, self.address, value, data, out_offset, out_size)

    def REVERT(self, offset, size):
        data = self.read_buffer(offset, size)
        raise Revert(data)

    def SELFDESTRUCT(self, to):
        '''Halt execution and register account for later deletion'''
        raise SelfDestruct(to)

    def __str__(self):
        def hexdump(src, length=16):
            FILTER = ''.join([(len(repr(chr(x))) == 3) and chr(x) or '.' for x in range(256)])
            lines = []
            for c in xrange(0, len(src), length):
                chars = src[c:c+length]
                def p (x):
                    if issymbolic(x):
                        return '??'
                    else:
                        return "%02x" % x 
                hex = ' '.join([p(x) for x in chars])
                def p1 (x):
                    if issymbolic(x):
                        return '.'
                    else:
                        return "%s" % ((x <= 127 and FILTER[x]) or '.') 

                printable = ''.join([p1(x) for x in chars])
                lines.append("%04x  %-*s  %s" % (c, length*3, hex, printable))
            return lines

        m = []
        if len(self.memory._memory.keys()):
            for i in range(max([0] + self.memory._memory.keys())+1):
                c = self.memory.read(i,1)[0]
                m.append(c)

        hd = hexdump(m)
        result = ['-'*147]
        if issymbolic(self.pc):
            result.append( '<Symbolic PC>')

        else:
            result.append( '0x%04x: %s %s %s\n'%(self.pc, self.instruction.name, self.instruction.has_operand and '0x%x'%self.instruction.operand or '', self.instruction.description))


        result.append('Stack                                                                      Memory')
        sp =0        
        for i in list(reversed(self.stack))[:10]:
            r = ''
            if issymbolic(i):
                r = '%s %r'%(sp==0 and 'top> ' or '     ', i)
            else:
                r = '%s 0x%064x'%(sp==0 and 'top> ' or '     ', i)
            sp+=1

            h = ''
            try:
                h = hd[sp-1]
            except:
                pass
            r +=  ' '*(75-len(r)) + h
            result.append(r)

        for i in range(sp,len(hd)):
            r =  ' '*75 + hd[i]
            result.append(r)

        result = [hex(self.address) +": "+x for x in result]
        return '\n'.join(result)

################################################################################
################################################################################
################################################################################
################################################################################
class EVMWorld(Platform):
    _published_events = {'evm_read_storage', 'evm_write_storage', 'evm_read_code', 'decode_instruction', 'execute_instruction', 'concrete_sha3', 'symbolic_sha3'} 

    def __init__(self, constraints, storage=None, **kwargs):
        super(EVMWorld, self).__init__(path="NOPATH", **kwargs)
        self._global_storage = {} if storage is None else storage
        self._constraints = constraints
        self._callstack = [] 
        self._deleted_address = set()
        self._logs = list()
        self._sha3 = {}
        self._pending_transaction = None
        self._transactions = list()
        self._internal_transactions = list()

    def __getstate__(self):
        state = super(EVMWorld, self).__getstate__()
        state['sha3'] = self._sha3
        state['pending_transaction'] = self._pending_transaction
        state['logs'] = self._logs
        state['storage'] = self._global_storage
        state['constraints'] = self._constraints
        state['callstack'] = self._callstack
        state['deleted_address'] = self._deleted_address
        state['transactions'] = self._transactions
        state['internal_transactions'] = self._internal_transactions
        return state

    def __setstate__(self, state):
        super(EVMWorld, self).__setstate__(state)
        self._sha3 = state['sha3']
        self._pending_transaction = state['pending_transaction']
        self._logs = state['logs'] 
        self._global_storage = state['storage']
        self._constraints = state['constraints']
        self._callstack = state['callstack']
        self._deleted_address = state['deleted_address']
        self._transactions = state['transactions']
        self._internal_transactions = state['internal_transactions']
        self._do_events()

    def _do_events(self):
        if self.current is not None:
            self.forward_events_from(self.current)
            self.subscribe('on_concrete_sha3', self._concrete_sha3_callback)

    def _concrete_sha3_callback(self, buf, value):
        if buf in self._sha3:
            assert self._sha3[buf] == value
        self._sha3[buf] = value

    def __getitem__(self, index):
        assert isinstance(index, (int,long))
        return self.storage[index]


    def __str__(self):
        return "WORLD:" + str(self._global_storage)
        
    @property
    def logs(self):
        return self._logs

    @property
    def constraints(self):
        return self._constraints

    @property
    def transactions(self):
        return self._transactions

    @property
    def internal_transactions(self):
        number_of_transactions = len(self._transactions)
        for _ in range( len (self._internal_transactions), number_of_transactions):
            self._internal_transactions.append([])
        return self._internal_transactions

    @property
    def all_transactions(self):
        txs = []
        for tx in self._transactions:
            txs.append(tx)
            for txi in self.internal_transactions[self._transactions.index(tx)]:
                txs.append(txi)
        return txs


    @property
    def last_return_data(self):
        return self.transactions[-1].return_data

    @constraints.setter
    def constraints(self, constraints):
        self._constraints = constraints
        for addr in self.storage:
            if isinstance(self.storage[addr]['storage'], EVMMemory): 
                self.storage[addr]['storage'].constraints = constraints
        if self.current:
            self.current.constraints = constraints


    @property
    def current(self):
        try:
            return self._callstack[-1]
        except IndexError:
            return None

    @property
    def accounts(self):
        return self.storage.keys()

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
    def deleted_addresses(self):
        return self._deleted_address

    @property
    def storage(self):
        if self.depth:
            return self.current.global_storage
        else:
            return self._global_storage

    def set_storage_data(self, address, offset, value):
        self.storage[address]['storage'][offset] = value

    def get_storage_data(self, address, offset):
        return self.storage[address]['storage'].get(offset)

    def get_storage_items(self, address):
        return self.storage[address]['storage'].items()

    def has_storage(self, address):
        return len(self.storage[address]['storage'].items()) != 0

    def set_balance(self, address, value):
        self.storage[int(address)]['balance'] = value

    def get_balance(self, address):
        return self.storage[address]['balance']

    def add_to_balance(self, address, value):
        self.storage[address]['balance'] += value

    def get_code(self, address):
        return self.storage[address]['code']

    def set_code(self, address, data):
        self.storage[address]['code'] = data

    def has_code(self, address):
        return len(self.storage[address]['code']) > 0


    def log(self, address, topic, data):
        self.logs.append((address, data, topics))
        logger.info('LOG %r %r', memlog, topics)

    def log_storage(self, addr):
        pass

    def add_refund(self, value):
        pass

    def block_prevhash(self):
        return 0

    def block_coinbase(self):
        return 0

    def block_timestamp(self):
        return 0

    def block_number(self):
        return  0

    def block_difficulty(self):
        return 0

    def block_gas_limit(self):
        return 0

    def tx_origin(self):
        return self.current_vm.origin

    def tx_gasprice(self):
        return 0

    #CALLSTACK
    def _push_vm(self, vm):
        #Storage address ->  account(value, local_storage)
        vm.global_storage = self.storage
        vm.global_storage[vm.address]['storage'] = copy.copy(self.storage[vm.address]['storage'])
        if self.depth:
            self.current.constraints = None
        #MAKE A DEEP COPY OF THE SPECIFIC ACCOUNT
        self._callstack.append(vm)
        self.current.depth = self.depth
        self.current.constraints = self.constraints
        #self.forward_events_from(self.current)
        self._do_events()
        if self.depth > 1024:
            while self.depth >0:
                self._pop_vm(rollback=True)
            raise TerminateState("Maximum call depth limit is reached", testcase=True)

    def _pop_vm(self, rollback=False):
        vm = self._callstack.pop()
        assert self.constraints == vm.constraints
        if self.current:
            self.current.constraints = vm.constraints

        if not rollback:
            if self.depth:
                self.current.global_storage = vm.global_storage
                self.current.logs += vm.logs
                self.current.suicides = self.current.suicides.union(vm.suicides)
            else:
                self._global_storage = vm.global_storage
                self._deleted_address = self._deleted_address.union(vm.suicides)
                self._logs += vm.logs
                for address in self._deleted_address:
                    del self.storage[address]
        return vm

    @property
    def depth(self):
        return len(self._callstack)

    def new_address(self):
        ''' create a fresh 160bit address '''
        new_address = random.randint(100, pow(2, 160))
        if new_address in self._global_storage.keys():
            return self.new_address()
        return new_address

    def execute(self):
        self._process_pending_transaction()
        try:
            if self.current is None:
                raise TerminateState("Trying to execute an empty transaction", testcase=False)
            self.current.execute()
        except Create as ex:
            self.CREATE(ex.value, ex.data)
        except Call as ex:
            self.CALL(ex.gas, ex.to, ex.value, ex.data)
        except Stop as ex:
            self.STOP()
        except Return as ex:
            self.RETURN(ex.data)
        except Revert as ex:
            self.REVERT(ex.data)
        except SelfDestruct as ex:
            self.SELFDESTRUCT(ex.to)
        except Sha3 as ex:
            self.HASH(ex.data)
        except EVMException as e:
            self.THROW()
        except Exception:
            raise


    def run(self):
        try:
            while True:
                self.execute()
        except TerminateState as e:
            if self.depth == 0 and e.message == 'RETURN':
                return self.last_return
            raise e

    def create_account(self, address=None, balance=0, code='', storage=None):
        ''' code is the runtime code '''
        storage = {} if storage is None else storage

        if address is None:
            address = self.new_address()
        assert address not in self.storage.keys(), 'The account already exists'
        self.storage[address] = {}
        self.storage[address]['nonce'] = 0L
        self.storage[address]['balance'] = balance
        self.storage[address]['storage'] = storage
        self.storage[address]['code'] = code

        return address

    def create_contract(self, origin=None, price=0, address=None, caller=None, balance=0, init='', run=False, header=None):
        assert len(init) > 0
        '''
        The way that the Solidity compiler expects the constructor arguments to 
        be passed is by appending the arguments to the byte code produced by the
        Solidity compiler. The arguments are formatted as defined in the Ethereum
        ABI2. The arguments are then copied from the init byte array to the EVM 
        memory through the CODECOPY opcode with appropriate values on the stack.
        This is done when the byte code in the init byte array is actually run 
        on the network.
        '''
        assert self._pending_transaction is None
        if caller is None and origin is not None:
            caller = origin
        if origin is None and caller is not None:
            origin = caller
        assert caller == origin
        if header is None:
            header = {'timestamp' : 0,
                      'number': 0,
                      'coinbase': 0,
                      'gaslimit': 0,
                      'difficulty':0
                }

        assert  not issymbolic(address) 
        assert  not issymbolic(origin) 
        address = self.create_account(address, 0)
  
        self.storage[address]['storage'] = EVMMemory(self.constraints, 256, 256)

        self._pending_transaction = ('Create', address, origin, price, '', origin, balance, ''.join(init), header)

        if run:
            assert False
            #run initialization code
            #Assert everything is concrete?
            assert  not issymbolic(origin) 
            assert  not issymbolic(address) 
            assert self.storage[origin]['balance'] >= balance
            runtime = self.run()
            self.storage[address]['code'] = ''.join(runtime)

        return address

    def CREATE(self, value, bytecode):
        origin = self.current.origin
        caller = self.current.address
        price = self.current.price
        self.create_contract(origin, price, address=None, balance=value, init=bytecode, run=False)
        self._process_pending_transaction()


    def transaction(self, address, origin=None, price=0, data='', caller=None, value=0, header=None, run=False):
        assert self._pending_transaction is None
        if caller is None and origin is not None:
            caller = origin
        if origin is None and caller is not None:
            origin = caller

        if address not in self.accounts or\
           caller not in self.accounts or \
           origin != caller and origin not in self.accounts:
            raise TerminateState('Account does not exist %x'%address, testcase=True)

        if header is None:
            header = {'timestamp' : 0,
                      'number': 0,
                      'coinbase': 0,
                      'gaslimit': 0,
                      'difficulty':0
                }
        if any([ isinstance(data[i], Expression) for i in range(len(data))]): 
            data_symb = self._constraints.new_array(index_bits=256, index_max=len(data))
            for i in range(len(data)):
                data_symb[i] = Operators.ORD(data[i])
            data = data_symb
        else:
            data = ''.join(data)
        bytecode = self.get_code(address)
        self._pending_transaction = ('Call', address, origin, price, data, caller, value, bytecode, header)

        if run:
            assert self.depth == 0
            assert  not issymbolic(caller) 
            assert  not issymbolic(address) 
            assert self.get_balance(caller) >= value
            #run contract
            #Assert everything is concrete?
            try:
                return self.run()
            except TerminateState:
                #FIXME better use of exceptions!
                pass

    def _process_pending_transaction(self):
        if self._pending_transaction is None:
            return
        assert self.current is None or self.current.last_exception is not None

        ty, address, origin, price, data, caller, value, bytecode, header = self._pending_transaction


        src_balance = self.get_balance(caller) #from
        dst_balance = self.get_balance(address) #to

        #discarding absurd amount of ether (no ether overflow)
        self.constraints.add(src_balance + value >= src_balance)

        failed = False

        if self.depth > 1024:
            failed=True

        if not failed:
            enough_balance = src_balance >= value
            if issymbolic(enough_balance):
                enough_balance_solutions = solver.get_all_values(self._constraints, enough_balance)

                if set(enough_balance_solutions) == set([True, False]): 
                    raise Concretize('Forking on available funds',
                                     expression = src_balance < value,
                                     setstate=lambda a,b: None,
                                     policy='ALL')

                if set(enough_balance_solutions) == set([False]):
                    failed = True
            else:
                if not enough_balance:
                    failed = True

        self._pending_transaction=None


        if ty == 'Create': 
            data = bytecode
 
        is_human_tx = ( self.depth == 0 )

        if failed:
            if is_human_tx: #human transaction
                tx = Transaction(ty, address, origin, price, data, caller, value, 'TXERROR', None)
                self._transactions.append(tx)
                raise TerminateState('TXERROR')
            else:
                self.current._push(0)
                return

        #Here we have enoug funds and room in the callstack

        self.storage[address]['balance'] += value
        self.storage[caller]['balance'] -= value

        new_vm = EVM(self._constraints, address, origin, price, data, caller, value, bytecode, header, global_storage=self.storage)
        self._push_vm(new_vm)


        tx = Transaction(ty, address, origin, price, data, caller, value, None, None)
        if is_human_tx:
            #handle human transactions
            if ty == 'Create':
                self.current.last_exception = Create(None, None, None)
            elif ty == 'Call':
                self.current.last_exception = Call(None, None, None, None)

            self._transactions.append(tx)
        else:            
            n = len(self._transactions)
            if len (self._internal_transactions) < n:
                self._internal_transactions.append([])
            self._internal_transactions[n].append(tx)


    def CALL(self, gas, to, value, data):
        address = to
        origin = self.current.origin
        caller = self.current.address
        price = self.current.price
        depth = self.depth + 1
        bytecode = self.get_code(to)
        self.transaction(address, origin, price, data, caller, value)
        self._process_pending_transaction()


    def RETURN(self, data):
        prev_vm = self._pop_vm() #current VM changed!
        if self.depth == 0:
            tx = self._transactions[-1]
            tx.return_data=data
            tx.result = 'RETURN'
            raise TerminateState("RETURN", testcase=True)


        last_ex = self.current.last_exception
        self.current.last_exception = None
        assert isinstance(last_ex, (Call, Create))

        if isinstance(last_ex, Create):
            self.current._push(prev_vm.address)
            self.set_code(prev_vm.address, data)
        else:
            size = min(last_ex.out_size, len(data))
            self.current.write_buffer(last_ex.out_offset, data[:size])
            self.current._push(1)
        #we are still on the CALL/CREATE
        self.current.pc += self.current.instruction.size

    def STOP(self):
        prev_vm = self._pop_vm(rollback=False)
        if self.depth == 0:
            tx = self._transactions[-1]
            tx.return_data=None
            tx.result = 'STOP'
            raise TerminateState("STOP", testcase=True)
        self.current.last_exception = None
        self.current._push(1)

        #we are still on the CALL/CREATE
        self.current.pc += self.current.instruction.size

    def THROW(self):
        prev_vm = self._pop_vm(rollback=True)
        #revert balance on CALL fail
        self.storage[prev_vm.caller]['balance'] += prev_vm.value
        self.storage[prev_vm.address]['balance'] -= prev_vm.value

        if self.depth == 0:
            tx = self._transactions[-1]
            tx.return_data=None
            tx.result = 'THROW'
            raise TerminateState("THROW", testcase=True)

        self.current.last_exception = None
        self.current._push(0)
        #we are still on the CALL/CREATE
        self.current.pc += self.current.instruction.size

    def REVERT(self, data):
        prev_vm = self._pop_vm(rollback=True)
        #revert balance on CALL fail
        self.storage[prev_vm.caller]['balance'] += prev_vm.value
        self.storage[prev_vm.address]['balance'] -= prev_vm.value

        if self.depth == 0:
            tx = self._transactions[-1]
            tx.return_data=data
            tx.result = 'REVERT'
            raise TerminateState("REVERT", testcase=True)

        self.current.last_exception = None
        #we are still on the CALL/CREATE
        self.current.pc += self.current.instruction.size

    def SELFDESTRUCT(self, recipient):
        #This may create a user account
        recipient = Operators.EXTRACT(recipient, 0, 160)
        address = self.current.address
        if recipient not in self.storage.keys():
            self.create_account(address=recipient, balance=0, code='', storage=None)
        self.storage[recipient]['balance'] += self.storage[address]['balance']
        self.storage[address]['balance'] = 0
        self.current.suicides.add(address)
        prev_vm = self._pop_vm(rollback=False)

        if self.depth == 0:
            tx = self._transactions[-1]
            tx.result = 'SELFDESTRUCT'
            raise TerminateState("SELFDESTRUCT", testcase=True)
            
    def HASH(self, data):

        def compare_buffers(a, b):
            if len(a) != len(b):
                return False
            cond = True
            for i in range(len(a)):
                cond = Operators.AND(a[i]==b[i], cond)
                if cond is False:
                    return False
            return cond

        assert any(map(issymbolic, data))
        logger.info("SHA3 Searching over %d known hashes", len(self._sha3))
        logger.info("SHA3 TODO save this state for future explorations with more known hashes")
        #Broadcast the signal 
        self._publish('on_symbolic_sha3', data, self._sha3.items())

        results = []

        #If know_hashes is true then there is a _known_ solution for the hash
        known_hashes = False
        for key, value in self._sha3.items():
            assert not any( map(issymbolic, key))
            cond = compare_buffers(key, data)
            if solver.can_be_true(self._constraints, cond):
                results.append((cond, value))  
                known_hashes = Operators.OR(cond, known_hashes)
        #results contains all the possible and known solutions


        #If known_hashes can be False then data can take at least one concrete 
        #value of which we do not know a hash for.

        #Calculate the sha3 of one extra example solution and add this as a 
        #potential result
        #This is an incomplete result:
        # Intead of choosing one single extra concrete solution we should save 
        # the state and when a new sha3 example is found load it back and try 
        #the new concretization for sha3.
        
        with self._constraints as temp_cs:
            if solver.can_be_true(temp_cs, Operators.NOT(known_hashes)):
                temp_cs.add(Operators.NOT(known_hashes))
                #a_buffer is different from all strings we know a hash for 
                a_buffer = solver.get_value(temp_cs, data)
                cond = compare_buffers(a_buffer, data)
                #Get the sha3 for a_buffer
                a_value = int(sha3.keccak_256(a_buffer).hexdigest(), 16)
                #add the new sha3 pair to the known_hashes and result
                self._publish('on_concrete_sha3', a_buffer, a_value)
                results.append((cond, a_value))
                known_hashes = Operators.OR(cond, known_hashes)
        
        if solver.can_be_true(self._constraints, known_hashes):
            self._constraints.add(known_hashes)
            value = 0 #never used
            for cond, sha in results:
                value = Operators.ITEBV(256, cond, sha, value)
        else:
            raise TerminateState("Unknown hash")
            
        self.current._push(value)
        self.current.pc += self.current.instruction.size

