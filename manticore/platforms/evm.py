'''
Solidity / Smart contract VM
Implements the yellow paper: http://gavwood.com/paper.pdf
Get example contracts from here:
https://ethereum.github.io/browser-solidity/#version=soljson-latest.js
'''
import random, copy
from ..platforms.platform import *
from ..core.smtlib import Expression, Bool, BitVec, Array, Operators, Constant, BitVecConstant, ConstraintSet
from ..core.smtlib.expression import *

from ..utils.helpers import issymbolic
from ..utils.event import Eventful
from ..core.smtlib.visitors import pretty_print, arithmetic_simplifier, translate_to_smtlib
from ..core.state import Concretize,TerminateState
from decimal import Decimal
from itertools import starmap
import types
import logging
import sys, hashlib
if sys.version_info < (3, 6):
    import sha3

logger = logging.getLogger('PLATFORM')

TT256 = 2 ** 256
TT256M1 = 2 ** 256 - 1
TT255 = 2 ** 255

def to_signed(i):
    return i if i < TT255 else i - TT256

def pack(i, size=32):
    assert size >=1
    o = [0] * size
    for x in range(size):
        o[(size-1) - x] = i & 0xff
        i >>= 8
    return ''.join(map(chr,o))

class EVMMemory(object):
    '''
    The EVM symbolic memory manager.
    '''
    def __init__(self, constraints, *args, **kwargs):
        '''
        Builds a memory.

        :param constraints:  a set of constraints
        :param symbols: Symbolic chunks
        '''
        assert isinstance(constraints, ConstraintSet)
        self._constraints = constraints
        self._allocated = 0
        self._symbols = {}
        self._memory = {}

    

    def __reduce__(self):
        return (self.__class__, (self.constraints, ), {'_symbols':self._symbols, '_allocated':self._allocated, '_memory':self._memory } )

    @property
    def constraints(self):
        return self._constraints

    @constraints.setter
    def constraints(self, constraints):
        self._constraints = constraints

    def _get_size(self, size):
        if isinstance(size, BitVec):
            size = arithmetic_simplifier(size)
        else:
            size = BitVecConstant(256, size)
        assert isinstance(size, BitVecConstant)
        return size.value

    def __str__(self):
        m = []
        if len(self._memory.keys()):
            for i in range(max([0] + self._memory.keys())+1):
                c = self.read(i,1)[0]
                if issymbolic(c):
                    c = '?'
                m.append(c)
        return ''.join(m)

    def allocate(self, address):
        '''
            Allocate more memory
        '''
        new_max = address % 32
        self._allocated = Operators.ITEBV(256, self._allocated < new_max, new_max, self._allocated)

    def _concrete_read(self, address):
        return self._memory.get(address, '\x00')

    def _concrete_write(self, address, value):
        assert not issymbolic(address) 
        assert not issymbolic(value)
        assert (ord(value) & (~0xff)) == 0 , "Not a byte"
        self._memory[address] = value

    def read(self, address, size):
        '''
        Read a stream of potentially symbolic bytes from a potentially symbolic
        address

        :param address: Where to read from
        :param size: How many bytes
        :rtype: list
        '''
        size = self._get_size(size)
        assert not issymbolic(size)

        if issymbolic(address):
            assert solver.check(self.constraints)
            logger.debug('Reading %d bytes from symbolic address %s', size, address)
            try:
                solutions = solver.get_all_values(self.constraints, address, maxcnt=0x1000) #if more than 0x3000 exception
            except TooManySolutions as e:
                m, M = solver.minmax(self.constraints, address)
                logger.debug('Got TooManySolutions on a symbolic read. Range [%x, %x]. Not crashing!', m, M)

                crashing_condition = True
                for start, end, perms, offset, name  in self.mappings():
                    if start <= M+size and end >= m :
                        if 'r' in perms:
                            crashing_condition = Operators.AND(Operators.OR( (address+size).ult(start), address.uge(end) ), crashing_condition)

                if solver.can_be_true(self.constraints, crashing_condition):
                    raise InvalidSymbolicMemoryAccess(address, 'r', size, crashing_condition)


                #INCOMPLETE Result! We could also fork once for every map
                logger.info('INCOMPLETE Result! Using the sampled solutions we have as result')
                condition = False
                for base in e.solutions:
                    condition = Operators.OR(address == base, condition )
                raise ForkState(condition)

            #So here we have all potential solutions to address
            assert len(solutions) > 0
            

            crashing_condition = False
            for base in solutions:
                if any(not self.access_ok(i, 'r') for i in xrange(base, base + size, self.page_size)):
                    crashing_condition = Operators.OR(address == base, crashing_condition)

            if solver.can_be_true(self.constraints, crashing_condition):
                raise InvalidSymbolicMemoryAccess(address, 'r', size, crashing_condition)

            condition = False
            for base in solutions:
                condition = Operators.OR(address == base, condition )

            result = []
            #consider size ==1 to read following code
            for offset in range(size):
                #Given ALL solutions for the symbolic address
                for base in solutions:
                    addr_value = base + offset
                    byte = Operators.ORD(self._concrete_read(addr_value))
                    if addr_value in self._symbols:
                        for condition, value in self._symbols[addr_value]:
                            byte = Operators.ITEBV(8, condition, Operators.ORD(value), byte)
                    if len(result) > offset:
                        result[offset] = Operators.ITEBV(8, address == base, byte, result[offset])
                    else:
                        result.append(byte)
                    assert len(result) == offset+1
            return map(Operators.CHR, result)
        else:
            result = []
            for i in range(size):
                result.append(self._concrete_read(address+i))
            for offset in range(size):
                if address+offset in self._symbols:
                    for condition, value in self._symbols[address+offset]:
                        if condition is True:
                            result[offset] = Operators.ORD(value)
                        else:
                            result[offset] = Operators.ITEBV(8, condition, Operators.ORD(value), result[offset])
            return map(Operators.CHR, result)

    def write(self, address, value):
        '''
        Write a value at address.
        :param address: The address at which to write
        :type address: int or long or Expression
        :param value: Bytes to write
        :type value: str or list
        '''
        size = len(value)
        #FIXME consider calling self.allocate?
        if issymbolic(address):

            solutions = solver.get_all_values(self.constraints, address, maxcnt=0x1000) #if more than 0x3000 exception

            crashing_condition = False
            for base in solutions:
                if any(not self.access_ok(i, 'w') for i in xrange(base, base + size, self.page_size)):
                    crashing_condition = Operators.OR(address == base, crashing_condition)

            if solver.can_be_true(self.constraints, crashing_condition):
                raise InvalidSymbolicMemoryAccess(address, 'w', size, crashing_condition)

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





class EVMInstruction(object):
    '''This represents an EVM instruction '''
    def __init__(self, opcode, name, operand_size, pops, pushes, description, operand=None):
        self._opcode = opcode 
        self._name = name 
        self._operand_size = operand_size
        self._pops = pops
        self._pushes = pushes
        self._description = description
        self._operand = operand           #Immediate operand if any
    
    def parse_operand(self, buf):
        operand = 0
        for _ in range(self.operand_size):
            operand <<= 8
            operand |= ord(next(buf))
        self._operand = operand

    @property
    def operand_size(self):
        return self._operand_size

    @property
    def has_operand(self):
        return self.operand_size > 0

    @property
    def operand(self):
        return self._operand

    @property
    def pops(self):
        return self._pops

    @property
    def pushes(self):
        return self._pushes

    @property
    def size(self):
        return self._operand_size + 1

    def __len__(self):
        return self.size

    @property
    def name(self):
        if self._name == 'PUSH':
            return 'PUSH%d'%self.operand_size
        elif self._name == 'DUP':
            return 'DUP%d'%self.pops
        elif self._name == 'SWAP':
            return 'SWAP%d'%(self.pops-1)
        elif self._name == 'LOG':
            return 'LOG%d'%(self.pops-2)
        return self._name

    def __str__(self):
        bytes = self.bytes.encode('hex')

        output = '<%s> '%bytes + self.name + (' 0x%x'%self.operand if self.has_operand else '')
        if True:
            output += ' '*(80-len(output))+self.description
        return output

    @property
    def semantics(self):
        return self._name

    @property
    def description(self):
        return self._description

    @property
    def bytes(self):
        bytes = []
        bytes.append(chr(self._opcode))
        for offset in reversed(xrange(self.operand_size)):
            c = (self.operand >> offset*8 ) & 0xff 
            bytes.append(chr(c))
        return ''.join(bytes)
        
class EVMDecoder(object):
    ''' 
        EVM Instruction factory
    '''
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
                0x80: ('DUP', 0, 1, 2, 0, 'Duplicate 1st stack item.'),
                0x81: ('DUP', 0, 2, 3, 0, 'Duplicate 2nd stack item.'),
                0x82: ('DUP', 0, 3, 4, 0, 'Duplicate 3rd stack item.'),
                0x83: ('DUP', 0, 4, 5, 0, 'Duplicate 4th stack item.'),
                0x84: ('DUP', 0, 5, 6, 0, 'Duplicate 5th stack item.'),
                0x85: ('DUP', 0, 6, 7, 0, 'Duplicate 6th stack item.'),
                0x86: ('DUP', 0, 7, 8, 0, 'Duplicate 7th stack item.'),
                0x87: ('DUP', 0, 8, 9, 0, 'Duplicate 8th stack item.'),
                0x88: ('DUP', 0, 9, 10, 0, 'Duplicate 9th stack item.'),
                0x89: ('DUP', 0, 10, 11, 0, 'Duplicate 10th stack item.'),
                0x8a: ('DUP', 0, 11, 12, 0, 'Duplicate 11th stack item.'),
                0x8b: ('DUP', 0, 12, 13, 0, 'Duplicate 12th stack item.'),
                0x8c: ('DUP', 0, 13, 14, 0, 'Duplicate 13th stack item.'),
                0x8d: ('DUP', 0, 14, 15, 0, 'Duplicate 14th stack item.'),
                0x8e: ('DUP', 0, 15, 16, 0, 'Duplicate 15th stack item.'),
                0x8f: ('DUP', 0, 16, 17, 0, 'Duplicate 16th stack item.'),
                0x90: ('SWAP', 0, 2, 2, 0, 'Exchange 1st and 2nd stack items.'),
                0x91: ('SWAP', 0, 3, 3, 0, 'Exchange 1st and 3rd stack items.'),
                0x92: ('SWAP', 0, 4, 4, 0, 'Exchange 1st and 4rd stack items.'),
                0x93: ('SWAP', 0, 5, 5, 0, 'Exchange 1st and 5rd stack items.'),
                0x94: ('SWAP', 0, 6, 6, 0, 'Exchange 1st and 6rd stack items.'),
                0x95: ('SWAP', 0, 7, 7, 0, 'Exchange 1st and 7rd stack items.'),
                0x96: ('SWAP', 0, 8, 8, 0, 'Exchange 1st and 8rd stack items.'),
                0x97: ('SWAP', 0, 9, 9, 0, 'Exchange 1st and 9rd stack items.'),
                0x98: ('SWAP', 0, 10, 10, 0, 'Exchange 1st and 10rd stack items.'),
                0x99: ('SWAP', 0, 11, 11, 0, 'Exchange 1st and 11rd stack items.'),
                0x9a: ('SWAP', 0, 12, 12, 0, 'Exchange 1st and 12rd stack items.'),
                0x9b: ('SWAP', 0, 13, 13, 0, 'Exchange 1st and 13rd stack items.'),
                0x9c: ('SWAP', 0, 14, 14, 0, 'Exchange 1st and 14rd stack items.'),
                0x9d: ('SWAP', 0, 15, 15, 0, 'Exchange 1st and 15rd stack items.'),
                0x9e: ('SWAP', 0, 16, 16, 0, 'Exchange 1st and 16rd stack items.'),
                0x9f: ('SWAP', 0, 17, 17, 0, 'Exchange 1st and 17th stack items.'),
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
                0xff: ('SELFDESTRUCT', 0, 1, 0, 0, 'Halt execution and register account for later deletion.')
            }


    @staticmethod
    def decode_one(bytecode):
        '''
        '''
        bytecode = iter(bytecode)
        opcode = ord(next(bytecode))
        invalid = ('INVALID', 0, 0, 0, 'Unknown opcode')
        name, operand_size, pops, pushes, gas, description = EVMDecoder._table.get(opcode, invalid)

        instruction = EVMInstruction(opcode, name, operand_size, pops, pushes, description)
        if instruction.has_operand:
            instruction.parse_operand(bytecode)

        return instruction

    @staticmethod
    def decode_all(bytecode):
        bytecode = iter(bytecode)
        while True:
            yield EVMDecoder.decode_one(bytecode)

    @staticmethod
    def disassemble(bytecode):
        output = ''
        address = 0
        for i in EVMDecoder.decode_all(bytecode) :
            output += "0x%04x %s\n"%(address, i)
            address += i.size
        return output

class EVMException(Exception):
    pass

class ConcretizeStack(EVMException):
    '''
    Raised when a symbolic memory cell needs to be concretized.
    '''
    def __init__(self, pos, expression, policy='MINMAX'):
        self.message = "Concretizing evm stack item {}".format(pos)
        self.pos = pos
        self.expression = expression

class StackOverflow(EVMException):
    ''' Attemped to push more than 1024 items '''
    pass

class StackUnderflow(EVMException):
    ''' Attemped to popo from an empty stack '''
    pass

class InvalidOpcode(EVMException):
    ''' Trying to execute invalid opcode '''
    pass


class Call(EVMException):
    def __init__(self, gas, to, value, in_offset, in_size, out_offset=0, out_size=0):
        self.gas = gas
        self.to = to
        self.value = value
        self.in_offset = in_offset
        self.in_size = in_size
        self.out_offset = out_offset
        self.out_size = out_size

    def __reduce__(self):
        return (self.__class__, (self.gas,self.to,self.value,self.in_offset,self.in_size,self.out_offset,self.out_size,) )


class Create(Call):
    def __init__(self, value, offset, size):
        super(Create, self).__init__(gas=None, to=None, value=value, in_offset=offset, in_size=size)

class DelegateCall(Call):
    pass

class Stop(EVMException):
    ''' Program reached a STOP instruction '''
    pass

class Return(EVMException):
    ''' Program reached a RETURN instruction '''
    def __init__(self, offset, size):
        self.offset = offset
        self.size = size

class Revert(EVMException):
    ''' Program reached a RETURN instruction '''
    def __init__(self, offset, size):
        self.offset = offset
        self.size = size
    def __reduce__(self):
        return (self.__class__, (self.offset,self.size) )

class SelfDestruct(EVMException):
    ''' Program reached a RETURN instruction '''
    def __init__(self, to):
        self.to = to

class NotEnoughGas(EVMException):
    ''' Not enough gas for operation '''
    pass

class Sha3(EVMException):
    def __init__(self, offset, size):
        self.offset = offset
        self.size = size


class EVM(Eventful):
    '''Machine State. The machine state is defined as
        the tuple (g, pc, m, i, s) which are the gas available, the
        program counter pc , the memory contents, the active
        number of words in memory (counting continuously
        from position 0), and the stack contents. The memory
        contents are a series of zeroes of bitsize 256
    '''

    def __init__(self, constraints, address, origin, price, data, caller, value, code, header, world=None, depth=0, **kwargs):
        '''
        memory, the initial memory
        address, the address of the account which owns the code that is executing.
        origin, the sender address of the transaction that originated this execution. A 160-bit code used for identifying Accounts.
        price, the price of gas in the transaction that originated this execution.
        data, the byte array that is the input data to this execution
        caller, the address of the account which caused the code to be executing. A 160-bit code used for identifying Accounts
        value, the value, in Wei, passed to this account as part of the same procedure as execution. One Ether is defined as being 10**18 Wei.
        bytecode, the byte array that is the machine code to be executed.
        header, the block header of the present block.
        depth, the depth of the present message-call or contract-creation (i.e. the number of CALLs or CREATEs being executed at present).

        '''
        super(EVM, self).__init__(**kwargs)
        self.constraints = constraints
        self.last_exception = None
        self.memory = EVMMemory(constraints)
        #self.constraints.new_array(256, 'MEM_%x_%d'%(address,depth))
        self.address = address
        self.origin = origin # always an account with empty associated code
        self.caller = caller # address of the account that is directly responsible for this execution
        self.coinbase = 0
        self.data = data
        self.price = price #This is gas price specified by the originating transaction
        self.value = value
        self.depth = depth
        self.bytecode = code
        self.suicide = set()

        #FIXME parse decode and mark invalid instructions
        #self.invalid = set()

        assert 'timestamp' in header
        self.header=header

        #Machine state
        self.pc = 0
        self.stack = []
        self.gas = 0
        self.global_storage = world
        self.allocated = 0

    def __getstate__(self):
        state = super(EVM, self).__getstate__()
        state['global_storage'] = self.global_storage
        state['constraints'] = self.constraints
        state['last_exception'] = self.last_exception
        state['memory'] = self.memory
        state['address'] = self.address
        state['origin'] = self.origin
        state['caller'] = self.caller
        state['coinbase'] = self.coinbase
        state['data'] = self.data
        state['price'] = self.price
        state['value'] = self.value
        state['depth'] = self.depth
        state['bytecode'] = self.bytecode
        state['pc'] = self.pc
        state['stack'] = self.stack
        state['gas'] = self.gas
        state['allocated'] = self.allocated
        state['suicide'] = self.suicide

        return state

    def __setstate__(self, state):
        self.global_storage = state['global_storage']
        self.constraints = state['constraints']
        self.last_exception = state['last_exception']
        self.memory = state['memory']
        self.address = state['address']
        self.origin = state['origin']
        self.caller = state['caller']
        self.coinbase = state['coinbase']
        self.data = state['data']
        self.price = state['price']
        self.value = state['value']
        self.depth = state['depth']
        self.bytecode = state['bytecode']
        self.pc = state['pc']
        self.stack = state['stack']
        self.gas = state['gas']
        self.allocated = state['allocated']
        self.suicide = state['suicide']
        super(EVM, self).__setstate__(state)

    #Memory related
    def _allocate(self, address):
        #print pretty_print (address)
        #if address > 100000:
        #    raise NotEnoughGas()
        self.memory.allocate(address)

    def _store(self, address, value):
        #CHECK ADDRESS IS A 256 BIT INT OR BITVEC
        #CHECK VALUE IS A 256 BIT INT OR BITVEC
        if address > 100000:
            raise NotEnoughGas()
        self._allocate(address)
        self.memory.write(address, [Operators.CHR(value)])

    def _load(self, address):
        self._allocate(address+32)
        value = Operators.ORD(self.memory.read(address,1)[0])
        #print pretty_print(value)
        value = arithmetic_simplifier(value)
        if isinstance(value, Constant) and not value.taint: 
            value = value.value
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
        return EVMDecoder.disassemble(self.bytecode)


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

        return EVMDecoder.decode_one(getcode())

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
        
    @property
    def current(self):
        return self

    #Execute an instruction from current pc
    def execute(self):  
        if issymbolic(self.pc):
            expression = self.pc
            def setstate(state, value):
                self.pc = value
            raise Concretize("Concretice PC",
                                expression=expression, 
                                setstate=setstate,
                                policy='ALL')


        self.publish('will_decode_instruction', self.pc)
        current = self.instruction

        self.publish('will_execute_instruction', current)

        implementation = getattr(self, current.semantics, None)
        if implementation is None:
            raise TerminateState("Instruction not implemented %s"%current.semantics, testcase=True)



        #Get arguments (imm, pop)
        arguments = []
        if self.instruction.has_operand:
            arguments.append(current.operand)
        for _ in range(current.pops):
            arguments.append(self._pop())

        self.publish('did_execute_instruction', current)

        #Execute
        try:
            result = implementation(*arguments)
        except ConcretizeStack as ex:
            for arg in reversed(arguments):
                self._push(arg)
            def setstate(state, value):
                self.stack[-ex.pos] = value
            raise Concretize("Concretice Stack Variable",
                                expression=ex.expression, 
                                setstate=setstate,
                                policy='ALL')
        except EVMException as e:
            self.last_exception = e
            raise

        self.publish('did_execute_instruction', self, current)

        
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
            result = a // b
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
        return Operators.ITEBV(256, a < b, 1, 0)

    def GT(self, a, b):
        '''Greater-than comparision'''
        return Operators.ITEBV(256, a > b, 1, 0)

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
        return Operators.EXTRACT(value, offset, 8)


    def SHA3(self, start, end):
        '''Compute Keccak-256 hash'''
        #read memory from start to end
        #calculate hash on it/ maybe remember in some structure where that hash came from
        #http://gavwood.com/paper.pdf
        raise Sha3(start, end)

    ##########################################################################
    ##Environmental Information
    def ADDRESS(self): 
        '''Get address of currently executing account     '''
        return self.address

    def BALANCE(self, account):
        '''Get balance of the given account'''
        value = self.global_storage[account & TT256M1 ]['balance']
        if value is None:
            return 0
        return value

    def ORIGIN(self): 
        '''Get execution origination address'''
        return self.origin

    def CALLER(self): 
        '''Get caller address'''
        return self.caller

    def CALLVALUE(self):
        '''Get deposited value by the instruction/transaction responsible for this execution'''
        return self.value

    def CALLDATALOAD(self, offset):
        '''Get input data of current environment'''
        #FIXME concretize offset?
        bytes = list(self.data[offset:offset+32])
        if len(bytes)<32:
            bytes += ['\x00'] * (32-len(bytes))
        bytes = map(Operators.ORD, bytes)
        value = Operators.CONCAT(256, *bytes)
        #FIXME: is this big end?
        return value 

    def CALLDATASIZE(self):
        '''Get size of input data in current environment'''
        return len(self.data)

    def CALLDATACOPY(self, mem_offset, data_offset, size):
        '''Copy input data in current environment to memory'''
        #FIXME put zero if not enough data
        size = arithmetic_simplifier(size)
        if issymbolic(size):
            raise ConcretizeStack(3, expression=size)
        
        for i in range(size):
            if data_offset+i < len(self.data):
                c = self.data[data_offset+i]
            else:
                c = '\x00'
            self._store(mem_offset+i, c)


    def CODESIZE(self):
        '''Get size of code running in current environment'''
        return len(self.bytecode)

    def CODECOPY(self, mem_offset, code_offset, size):
        '''Copy code running in current environment to memory'''
        if issymbolic(size):
            raise ConcretizeStack(3, expression=size)
        print "CODECOPY(self, ", mem_offset, code_offset, size
        for i in range(size):
            if (code_offset+i > len(self.bytecode)):
                self._store(mem_offset+i, 0)
            else:
                self._store(mem_offset+i, ord(self.bytecode[code_offset+i]))

    def GASPRICE(self):
        '''Get price of gas in current environment'''
        return self.price

    def EXTCODESIZE(self, account):
        '''Get size of an account's code'''
        #FIXME
        return len(self.global_storage[account & TT256M1]['code'])

    def EXTCODECOPY(self, account, address, offset, size): 
        '''Copy an account's code to memory'''
        #FIXME STOP! if not enough data
        extbytecode = self.global_storage[account& TT256M1]['code']
        for i in range(size):
            if offset + i < len(extbytecode):
                self._store(address+i, extbytecode[offset+i])
            else:
                self._store(address+i, 0)

    ##########################################################################
    ##Block Information
    def BLOCKHASH(self, a):
        '''Get the hash of one of the 256 most recent complete blocks'''
        #FIXME SHOULD query self.header structure
        #90743482286830539503240959006302832933333810038750515972785732718729991261126L,
        return 0

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

    def SLOAD(self, address):
        '''Load word from storage'''
        #FIXME implement system?
        return self.global_storage[self.address]['storage'].get(address,0)

    def SSTORE(self, address, value):
        '''Save word to storage'''
        #FIXME implement system?
        self.global_storage[self.address]['storage'][address] = value
        if value is 0:
            del self.global_storage[self.address]['storage'][address]

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
        return self.allocated

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
        memlog = []
        for i in range(size):
            memlog.append(self._load(address+i))
        logger.info('LOG %r %r', memlog, topics)
    
    ##########################################################################
    ##System operations
    def read_buffer(self, offset, size):
        
        buf = []
        for i in range(size):
            buf.append(Operators.CHR(self._load(offset+i)))
        return buf

    def write_buffer(self, offset, buf):
        count = 0
        for c in buf:
            self._store(offset+count, c)
            count +=1 

    def CREATE(self, value, offset, size):
        '''Create a new account with associated code'''
        raise Create(value, offset, size)

    def CALL(self, gas, to, value, in_offset, in_size, out_offset, out_size):
        '''Message-call into an account'''
        raise Call(gas, to, value, in_offset, in_size, out_offset, out_size)

    def CALLCODE(self, gas, to, value, in_offset, in_size, out_offset, out_size):
        '''Message-call into this account with alternative account's code'''
        raise Call(gas, self.address, value, in_offset, in_size, out_offset, out_size)

    def RETURN(self, offset, size):
        '''Halt execution returning output data'''
        raise Return(offset, size)

    def DELEGATECALL(self, gas, to, in_offset, in_size, out_offset, out_size):
        '''Message-call into this account with an alternative account's code, but persisting into this account with an alternative account's code'''
        value = 0
        raise Call(gas, self.address, value, in_offset, in_size, out_offset, out_size)

    def REVERT(self, offset, size):
        raise Revert(offset, size)

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
                        return "%02x" % ord(x) 
                hex = ' '.join([p(x) for x in chars])
                def p1 (x):
                    if issymbolic(x):
                        return '.'
                    else:
                        return "%s" % ((ord(x) <= 127 and FILTER[ord(x)]) or '.') 

                printable = ''.join([p1(x) for x in chars])
                lines.append("%04x  %-*s  %s" % (c, length*3, hex, printable))
            return lines

        m = []
        if len(self.memory._memory.keys()):
            for i in range(max([0] + self.memory._memory.keys())+1):
                c = self.memory.read(i,1)[0]
                m.append(c)

        hd = hexdump(m)
        result = ['Stack                                                                      Memory']
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
                h = hd[sp]
            except:
                pass
            r +=  ' '*(75-len(r)) + h
            result.append(r)

        for i in range(sp,len(hd)):
            r =  ' '*75 + hd[i]
            result.append(r)

        if issymbolic(self.pc):
            result.append( '<Symbolic PC>')

        else:
            result.append( '0x%04x: %s %s %s\n'%(self.pc, self.instruction.name, self.instruction.has_operand and '0x%x'%self.instruction.operand or '', self.instruction.description))
        result.append( '-'*147)
        return '\n'.join(result)



class EVMWorld(Platform):
    def __init__(self, constraints, storage=None, **kwargs):
        super(EVMWorld, self).__init__(path="NOPATH", **kwargs)
        self._global_storage = {} if storage is None else storage
        self._constraints = constraints
        self._callstack = [] 
        self._deleted_address = set()
        self._suicide = set()

    def __getstate__(self):
        state = super(EVMWorld, self).__getstate__()
        state['storage'] = self._global_storage
        state['constraints'] = self._constraints
        state['callstack'] = self._callstack
        state['deleted_address'] = self._deleted_address
        return state

    def __setstate__(self, state):
        super(EVMWorld, self).__setstate__(state)
        self._global_storage = state['storage']
        self._constraints = state['constraints']
        self._callstack = state['callstack']
        self._deleted_address = state['deleted_address']
        if self.current is not None:
            self.forward_events_from(self.current)

    def __str__(self):
        return "WORLD:" + str(self._global_storage)
        

    @property
    def constraints(self):
        return self._constraints

    @constraints.setter
    def constraints(self, constraints):
        self._constraints = constraints

    @property
    def current(self):
        try:
            return self._callstack[-1]
        except IndexError:
            return None

    @property
    def suicide(self):
        return self.current.suicide

    @property
    def storage(self):
        if self.depth:
            return self.current.global_storage
        else:
            return self._global_storage

    @storage.setter
    def storage(self, value):
        if self.depth:
            self.current.global_storage = value
        else:
            self._global_storage = value

    def _push(self, vm):
        vm.global_storage = copy.deepcopy(self.storage)
        self._callstack.append(vm)
        self.current.depth = self.depth
        self.forward_events_from(self.current)
        if self.depth > 1024:
            while self.depth >0:
                self._pop(rollback=True)
            raise TerminateState("Maximum call depth limit is reached", testcase=True)

    def _pop(self, rollback=False):
        vm = self._callstack.pop()

        if not rollback:
            self.storage = vm.global_storage
            if self.depth:
                self._suicide = self.suicide.union(vm.suicide)
            else: 
                for address in vm.suicide:
                    del self.storage[address]
        return vm

    @property
    def depth(self):
        return len(self._callstack)

    def _new_address(self):
        ''' create a fresh 160bit address '''
        new_address = random.randint(100, pow(2, 160))
        if new_address in self._global_storage.keys():
            return self._new_address()
        return new_address

    def execute(self):
        try:
            if self.current is None:
                raise TerminateState("No transaction", testcase=False)

            self.current.execute()
        except Create as ex:
            self.CREATE(ex.value, ex.in_offset, ex.in_size)
        except Call as ex:
            self.CALL(ex.gas, ex.to, ex.value, ex.in_offset, ex.in_size, ex.out_offset, ex.out_size)
        except Stop as ex:
            self.STOP()
        except Return as ex:
            self.RETURN(ex.offset, ex.size)
        except Revert as ex:
            self.REVERT()
        except SelfDestruct as ex:
            self.SELFDESTRUCT(ex.to)
        except Sha3 as ex:
            self.HASH(ex.offset, ex.size)
        except EVMException as e:
            self.THROW()

    def run(self):
        try:
            while True:
                self.execute()
        except TerminateState as e:
            if self.depth == 0 and e.message == 'RETURN':
                return self.last_return
            '''import traceback
            print "Exception in user code:"
            print '-'*60
            traceback.print_exc(file=sys.stdout)
            print '-'*60'''
            raise e

    def create_account(self, address=None, balance=0, code='', storage=None):
        ''' code is the runtime code '''
        if address is None:
            address = self._new_address()
        assert address not in self.storage.keys(), 'The account already exists'
        self.storage[address] = {}
        self.storage[address]['nonce'] = 0L
        self.storage[address]['balance'] = balance
        self.storage[address]['storage'] = {} if storage is None else storage
        self.storage[address]['code'] = code
        return address

    def create_contract(self, origin, price, address=None, balance=0, init='', run=False):
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
        address = self.create_account(address, balance)
        header = {'timestamp' : 0,
                  'number': 0,}
        new_vm = EVM(self._constraints, address, origin, price, '', origin, value=balance, code=init, header=header)
        new_vm.last_exception = Create(None, None, None)
        self._push(new_vm)
        if run:
            #run initialization code
            #Assert everything is concrete?
            runtime = self.run()
            self.storage[address]['code'] = ''.join(runtime)

        return address

    def transaction(self, address, origin, price, data, caller, value, header, run=False):
        assert self.depth == 0
        bytecode = self.storage[address]['code']
        new_vm = EVM(self._constraints, address, origin, price, data, caller, value, bytecode, header, world=self)
        self._push(new_vm)
        self.current.last_exception = Call(None,None,None,None,None,None,None)
        if run:
            #run contract
            #Assert everything is concrete?
            try:
                return self.run()
            except TerminateState:
                #FIXME better use of exceptions!
                pass

    def CREATE(self, value, offset, size):
        bytecode = self.current.read_buffer(offset, size)
        address = self._new_address()
        origin = self.current.origin
        caller = self.current.address
        price = self.current.price
        header = {'timestamp': 100}
        new_vm = EVM(self._constraints, address, origin, price, "", caller, value, bytecode, header)
        self._push(new_vm)
        self.storage[address] = {}

    def CALL(self, gas, to, value, in_offset, in_size, out_offset, out_size):
        data = self.current.read_buffer(in_offset, in_size)
        address = to
        origin = self.current.origin
        caller = self.current.address
        price = self.current.price
        depth = self.depth+1
        bytecode = self.storage[to]['code']
        header = {'timestamp' :1}
        new_vm = EVM(self._constraints, address, origin, price, data, caller, value, bytecode, header)
        self._push(new_vm)

    def RETURN(self, offset, size):
        data = self.current.read_buffer(offset, size)
        prev_vm = self._pop() #current VM changed!

        if self.depth == 0:
            self.last_return=data
            raise TerminateState("RETURN", testcase=True)

        last_ex = self.current.last_exception
        self.current.last_exception = None
        assert isinstance(last_ex, (Call, Create))

        if isinstance(last_ex, Create):
            self.current._push(prev_vm.address)
            self.storage[prev_vm.address]['code'] = data

        else:
            size = min(last_ex.out_size, size)
            self.current.write_buffer(last_ex.out_offset, data[:size])
            self.current._push(1)
        #we are still on the CALL/CREATE
        self.current.pc += self.current.instruction.size

    def STOP(self):
        self._pop(rollback=False)
        if self.depth == 0:
            raise TerminateState("STOP", testcase=True)
        self.current.last_exception = None
        self.current._push(1)

        #we are still on the CALL/CREATE
        self.current.pc += self.current.instruction.size

    def THROW(self):
        self._pop(rollback=True)
        if self.depth == 0:
            raise TerminateState("THROW", testcase=True)
        self.current.last_exception = None
        self.current._push(0)
        #we are still on the CALL/CREATE
        self.current.pc += self.current.instruction.size

    def REVERT(self):
        self._pop(rollback=True)
        if self.depth == 0:
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
        self.suicide.add(address)
        self._pop(rollback=False)
        if self.depth == 0:
            for address in self.suicide:
                del self.storage[address]
            raise TerminateState("SELFDESTRUCT", testcase=True)

    def HASH(self, offset, size):
        data = self.current.read_buffer(offset, size)
        if any(map(issymbolic, data)):
            value = self._constraints.new_bitvec(256, 'HASH')
        else:
            value = sha3.keccak_256(''.join(data)).hexdigest()
            value = int('0x'+value,0)
        self.current._push(value)
        self.current.pc += self.current.instruction.size
        


if __name__ == '__main__':
    bytecode='60606040526000357c0100000000000000000000000000000000000000000000000000000000900463ffffffff1680635ec01e4d146044578063e1c7392a146067575bfe5b3415604b57fe5b60516076565b6040518082815260200191505060405180910390f35b3415606e57fe5b60746080565b005b6000600490505b90565b5b5600a165627a7a723058201ee3d4d835c10d46b09531c20dcdfe17b2dcef676a2666d66d0b3dde4969f6e00029'.decode   ('hex')
    #print EVMDecoder.disassemble(bytecode)

    instructions = list(EVMDecoder.decode_all(bytecode))

    BBs = {}
    EDGES = {}
    current_bb = []
    address = 0
    for i in instructions:
        i.address = address

        current_bb.append(i)
        if i.name in ['JUMPI', 'JUMP', 'STOP', 'INVALID', 'RETURN', 'SELFDESTRUCT', 'REVERT']:
            BBs[current_bb[0].address] = tuple(current_bb)
            if i.name in ['JUMP', 'JUMPI']:
                source = current_bb[0].address
                if len(current_bb) >= 2:
                    if current_bb[-2].name.startswith('PUSH'):
                        dest = current_bb[-2].operand
                    EDGES.setdefault(source, set()).add(dest)
                    if i.name  == 'JUMPI':
                        EDGES[source].add(address + i.size)

            current_bb = list()
        address += i.size


    for addr in sorted(BBs.keys()):
        print hex(addr), ":",  map(hex, sorted(list(EDGES.get(addr,set()))))
        print '\n'.join(map(lambda x: "  "+str(x), BBs[addr]))
 
    address=0x414141414141
    origin=0x424242424242
    price=1
    data='AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA'
    sender=0x434343434343
    value=1
    header={'timestamp':1}
    depth=0

        
    from manticore.core.smtlib.constraints import ConstraintSet
    constraints = ConstraintSet()
    memory = constraints.new_array(256, 'MEM_%d'%depth)
    evm = EVM(memory, address, origin, price, data, sender, value, bytecode, header, depth)
    print evm
    import pickle
    a = pickle.dumps(evm)
    evm = pickle.loads(a)
    while True:
        evm.execute()  
        print evm

