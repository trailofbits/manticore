from capstone import *
from capstone.arm import *
from capstone.x86 import *
from unicorn import *
from unicorn.x86_const import *
from unicorn.arm_const import *
from abc import ABCMeta, abstractmethod
from ..smtlib import Expression, Bool, BitVec, Array, Operators, Constant
from ..memory import MemoryException
from ...utils.helpers import issymbolic
import sys
from functools import wraps
import types
import logging
logger = logging.getLogger("CPU")

######################################################################
# Abstract classes for capstone/unicorn based cpus
# no emulator by default
MU = {
        (CS_ARCH_ARM, CS_MODE_ARM): Uc(UC_ARCH_ARM, UC_MODE_ARM),
        (CS_ARCH_X86, CS_MODE_32): Uc(UC_ARCH_X86, UC_MODE_32),
        (CS_ARCH_X86, CS_MODE_64): Uc(UC_ARCH_X86, UC_MODE_64)
     }

SANE_SIZES = {8, 16, 32, 64, 80, 128, 256}
# This encapsulates how to acccess operands (regs/mem/immediates) for differents cpus
class Operand(object):

    class MemSpec(object):
        ''' Auxiliary class wraps capstone operand 'mem' attribute. This will return register names instead of Ids ''' 
        def __init__(self, parent):
            self.parent = parent
        segment = property( lambda self: self.parent._reg_name(self.parent.op.mem.segment) )
        base = property( lambda self: self.parent._reg_name(self.parent.op.mem.base) )
        index = property( lambda self: self.parent._reg_name(self.parent.op.mem.index) )
        scale = property( lambda self: self.parent.op.mem.scale )
        disp = property( lambda self: self.parent.op.mem.disp )

    def __init__(self, cpu, op, **kwargs):
        '''
        This encapsulates the arch way to access instruction operands and immediates based on a 
        capstone operand descriptor.
        This class knows how to browse a capstone operand and get the details of operand.
        It also knows how to access the specific Cpu to get the actual values from memory and registers.

        @param cpu:  A Cpu oinstance
        @param op: a Capstone operand (eew)
        '''
        assert isinstance(cpu, Cpu)
        assert isinstance(op, (X86Op, ArmOp))
        self.cpu = cpu
        self.op = op
        self.mem = Operand.MemSpec(self)

    def _reg_name(self, reg_id):
        ''' Translates a capstone register ID into the register name '''
        cs_reg_name = self.cpu.instruction.reg_name(reg_id)
        if cs_reg_name is None or cs_reg_name.lower() == '(invalid)':
            return None
        return self.cpu._regfile._alias(cs_reg_name.upper())

    def __getattr__(self, name):
        return getattr(self.op, name)

    @property
    def size(self):
        ''' Return bit size of operand '''
        raise NotImplementedError
        
    def address(self):
        ''' On a memory operand it returns the effective address '''
        raise NotImplementedError

    def read(self):
        ''' It reads the operand value from the registers or memory '''
        raise NotImplementedError

    def write(self, value):
        ''' It writes the value ofspecific type to the registers or memory '''
        raise NotImplementedError

# Basic register file structure not actully need to abstract as it's used only from the cpu implementation
class RegisterFile(object):

    def __init__(self, aliases=None):
        if aliases is None:
            aliases = {}
        self._aliases = aliases
        ''''dict mapping from alias register name ('PC') to actual register name ('RIP') '''

    def _alias(self, register):
        '''Get register canonical alias. ex. PC->RIP or PC->R15 '''
        return self._aliases.get(register, register) 

    #@abstractmethod
    def write(self, register, value):
        ''' Write value to the specified register 
            @param register: a register id. Must be listed on all_registers
            @param value: a value of the expected type
            @return the value actually written to the register
        '''
        pass

    #@abstractmethod
    def read(self, register):
        ''' Read value from specified register 
            @param register: a register name. Must be listed on all_registers
            @return the register value
        '''
        pass

    @property
    def all_registers(self):
        ''' Lists all possible register names (Including aliases) '''
        return tuple(self._aliases)

    @property
    def canonical_registers(self):
        ''' List the minimal most beautiful set of registers needed '''
        pass
        
    def __contains__(self, register):
        ''' Check for register validity 
            @param register: a register name
        '''
        return self._alias(register) in self.all_registers 
############################################################################
# Abstract cpu encapsulating common cpu methods used by models and executor.
class Cpu(object):
    '''
    This is an abstract representation of a Cpu. Functionality common to all
    architectures (and expected from users of a Cpu) should be here.

    The following attributes need to be defined in any derived class

    - arch
    - mode
    - max_instr_width
    - address_bit_size
    - pc_alias
    - stack_alias
    '''

    def __init__(self, regfile, memory):
        assert isinstance(regfile, RegisterFile)
        super(Cpu, self).__init__()
        self._regfile = regfile
        self._memory = memory
        self._instruction_cache = {}
        self._icount = 0

        self._md = Cs(self.arch, self.mode)
        self._md.detail = True
        self._md.syntax = 0
        self.instruction = None
        #FIXME self.transactions = []

    def __getstate__(self):
        state = {}
        state['regfile'] = self._regfile
        state['memory'] = self._memory
        state['icount'] = self._icount
        return state

    def __setstate__(self, state):
        Cpu.__init__(self, state['regfile'], state['memory'])
        self._icount = state['icount']
        return 

    @property
    def icount(self):
        return self._icount

    ##############################
    # Register access
    @property
    def regfile(self):
        ''' The RegisterFile of this cpu '''
        return self._regfile

    @property
    def all_registers(self):
        ''' Returns the list of all register names  for this CPU.
        @rtype: tuple
        @return: the list of register names for this CPU.
        '''
        return self._regfile.all_registers

    #this operates on names
    def write_register(self, register, value):
        ''' A convenient method to write a register by name (this accepts alias)
            @param register a register name as listed in all_registers
            @param value a value
            @return It will return the written value possibly croped
        '''
        return self._regfile.write(register, value)

    def read_register(self, register):
        ''' A convenient method to read a register by name (this accepts alias)
            @param register a register name as listed in all_registers
            @param value a value
            @return It will return the written value possibly croped
        '''
        return self._regfile.read(register)

    # Pythonic acces to registers and aliases
    def __getattr__(self, name):
        ''' A pythonic version of read_register '''
        assert name != '_regfile'
        if hasattr(self, '_regfile') and name in self._regfile:
            return self.read_register(name)
        raise AttributeError(name)

    def __setattr__(self, name, value):
        ''' A pythonic version of write_register '''
        if hasattr(self, '_regfile') and name in self._regfile:
            return self.write_register(name, value)
        object.__setattr__(self, name, value)
    

    #############################
    # Memory access
    @property
    def memory(self):
        return self._memory

    def write_int(self, where, expr, size=None):
        '''
        Writes int to memory

        :param int where: address to write to
        :param expr: value to write
        :type expr: int or BitVec
        :param size: bit size of `expr`
        '''
        if size is None:
            size = self.address_bit_size
        assert size in SANE_SIZES
        self.memory[where:where+size/8] = [Operators.CHR(Operators.EXTRACT(expr, offset, 8)) for offset in xrange(0, size, 8)]

    def read_int(self, where, size=None):
        '''
        Reads int from memory

        :param int where: address to read from
        :param size: number of bits to read
        :return: the value read
        :rtype: int or BitVec
        '''
        if size is None:
            size = self.address_bit_size
        assert size in SANE_SIZES
        data = self.memory[where:where+size/8]
        total_size = 8 * len(data)
        value = Operators.CONCAT(total_size, *map(Operators.ORD, reversed(data)))
        return value


    def write_bytes(self, where, data):
        '''
        Write a concrete or symbolic (or mixed) buffer to memory

        :param int where: address to write to
        :param data: data to write
        :type data: str
        '''
        for i in xrange(len(data)):
            self.write_int( where+i, Operators.ORD(data[i]), 8)

    def read_bytes(self, where, size):
        '''
        Reads from memory

        :param int where: address to read data from
        :param int size: number of bytes
        :return: data
        :rtype: list[int or Expression]
        '''
        result = []
        for i in xrange(size):
            result.append(Operators.CHR(self.read_int( where+i, 8)))
        return result

    #######################################
    # Decoder
    @abstractmethod
    def _wrap_operands(self, operands):
        ''' Private method to decorate a capston Operand to our needs. See Operand class'''
        pass

    def decode_instruction(self, pc):
        ''' This will decode an intructcion from memory pointed by @pc
            @param pc address of the instruction
        '''
        #No dynamic code!!! #TODO! 
        #Check if instruction was already decoded 
        self._instruction_cache = {}
        if pc in self._instruction_cache:
            logger.debug("Intruction cache hit at %x", pc)
            return self._instruction_cache[pc]

        text = ''
        try:
            # check access_ok
            for i in xrange(0, self.max_instr_width):
                c = self.memory[pc+i]
                if issymbolic(c):
                    assert isinstance(c, BitVec) and  c.size == 8
                    if isinstance(c, Constant):
                        c = chr(c.value)
                    else:
                        logger.error('Concretize executable memory %r %r', c, text )
                        break
                assert isinstance(c, str)
                text += c
        except MemoryException as e:
            pass
        
        code = text.ljust(self.max_instr_width, '\x00')
        instruction = next(self._md.disasm(code, pc))

        #PC points to symbolic memory 
        if instruction.size > len(text):
            logger.info("Trying to execute instructions from invalid memory")
            raise InvalidPCException(self.PC)

        if not self.memory.access_ok(slice(pc, pc+instruction.size), 'x'):
            logger.info("Trying to execute instructions from not executable memory")
            raise InvalidPCException(self.PC)
        instruction.operands = self._wrap_operands(instruction.operands)

        self._instruction_cache[pc] = instruction
        return instruction


    #######################################
    # Execute
    @abstractmethod
    def canonicalize_instruction_name(self, instruction):
        ''' Get the semantic name of an instruction. 
        The subyacent arch implementations'''
        pass

    def execute(self):
        ''' Decode, and execute one intruction pointed by register PC'''
        if not isinstance(self.PC, (int,long)):
            raise SymbolicPCException()

        if not self.memory.access_ok(self.PC,'x'):
            raise InvalidPCException(self.PC)

        instruction = self.decode_instruction(self.PC)
        self.instruction = instruction #FIX

        name = self.canonicalize_instruction_name(instruction)

        try:
            implementation = getattr(self, name)
        except AttributeError as ae:
            logger.debug("UNIMPLEMENTED INSTRUCTION: 0x%016x:\t%s\t%s\t%s", instruction.address, ' '.join(map(lambda x: '%02x'%x, instruction.bytes)), instruction.mnemonic, instruction.op_str)
            implementation = lambda *ops: self.emulate(instruction)

        #log
        if logger.level == logging.DEBUG :
            for l in str(self).split('\n'):
                logger.debug(l)
        implementation(*instruction.operands)
        self._icount+=1

    @abstractmethod
    def get_syscall_description(self):
        pass

    #############################################################
    # Emulation
    def _concretize_registers(self, instruction):
        pass

    def _unicorn(self):
        return MU[(self.arch, self.mode)]

    def emulate(self, instruction):
        #Fix Taint propagation
        needed_pages = set()
        needed_bytes = set()
        mapped = set()
        accessed = set()
        byte_values = {}

        reg_values = self._concretize_registers(instruction)
        # Request any memory nearby the memory directly needed by the memory
        # operands of the instruction. 
        for op in instruction.operands:
            if op.type != {CS_ARCH_ARM: ARM_OP_MEM, CS_ARCH_X86: X86_OP_MEM}[self.arch]:
                continue
            self.PC += instruction.size
            addr = op.address()  #FIXME maybe add a kwarg parameter to operand.address() with the current pc?
            self.PC -= instruction.size
            assert not issymbolic(addr)
            num_bytes = op.size/8
            needed_bytes.update(range(addr, addr + num_bytes))
        # Request the bytes of the instruction.
        needed_bytes.update(range(self.PC, self.PC + instruction.size))

        # Concretizes the bytes of memory potentially needed by the instruction.
        for addr in needed_bytes:
            needed_pages.add(addr & (~0xFFF))
            val = self.read_int(addr, 8)
            if issymbolic(val):
                logger.debug("Concretizing bytes before passing it to unicorn")
                raise ConcretizeMemory(addr, 8, "Passing control to emulator", 'SAMPLED')
            byte_values[addr] = val

        mu = self._unicorn()

        touched = set()
        def hook_mem_access(uc, access, address, size, value, user_data):
            if access & UC_MEM_WRITE:
                for i in range(address, address+size):
                    user_data.add(i)
            if access & UC_MEM_READ:
                for i in range(address, address+size):
                    if i not in needed_bytes:
                        logger.error("Not initalized memory used by emulator at %x", address)
        try:
            # Copy in the concrete values of all needed registers.
            for reg, value in reg_values.items():
                #stem = {CS_ARCH_ARM: 'UC_ARM_REG_', CS_ARCH_X86: 'UC_X86_REG_'}[self.arch]
                stem = 'UC_X86_REG_'
                mu.reg_write(globals()[stem+reg], value)

            #Map needed pages
            for page in needed_pages:
                mapped.add(page)
                mu.mem_map(page, 0x1000, UC_PROT_ALL)
            # Copy in memory bytes needed by instruction.
            for addr, value in byte_values.items():
                mu.mem_write(addr, Operators.CHR(value))

            # Run the instruction.
            hook_id = mu.hook_add(UC_HOOK_MEM_WRITE | UC_HOOK_MEM_READ, hook_mem_access, touched)
            mu.emu_start(self.PC, self.PC+instruction.size)
            mu.hook_del(hook_id)
            mu.emu_stop()

            # Copy back the memory modified by the unicorn emulation.
            for addr in touched:
                if not addr in needed_bytes:
                    logger.error("Some address was touched in the emulation but not provided %x", addr)
                assert addr in needed_bytes
                try:
                    cpu.write_int(addr, ord(mu.mem_read(addr, 1)), 8)
                except:
                    pass

            # Copy back the new values of all registers.
            if hasattr(instruction, 'regs_access') and instruction.regs_access is not None:
                (regs_read, regs_write) = instruction.regs_access()
                regs = [ instruction.reg_name(r).upper() for r in regs_write ] 
                if self.arch == CS_ARCH_X86:
                    regs += ['FPSW', 'FPCW', 'FPTAG', 'FP0', 'FP1', 'FP2', 'FP3', 'FP4', 'FP5', 'FP6', 'FP7']
            else:
                regs = reg_values.keys()
            logger.debug("Emulator wrote to this regs %r", regs)
            for reg in regs:
                #stem = {CS_ARCH_ARM: 'UC_ARM_REG_', CS_ARCH_X86: 'UC_X86_REG_'}[self.arch]
                stem = 'UC_X86_REG_'
                new_value = mu.reg_read(globals()[stem+reg])
                self.write_register(reg, new_value)
          
            self.PC = self.PC+instruction.size
            return
        except Exception as e:
            logger.error('Exception in emulatin code:')
            logger.error(e, exc_info=True)
        finally:
            for i in mapped:
                mu.mem_unmap(i,0x1000)

    #Generic string representation
    def __str__(self):
        '''
        Returns a string representation of cpu state
        
        @rtype: str
        @return: a string containing the name and current value for all the registers. 
        '''
        result = ""
        try:
            instruction = self.instruction
            result += "INSTRUCTION: 0x%016x:\t%s\t%s\n"%( instruction.address, instruction.mnemonic, instruction.op_str)
        except:
            result += "{can't decode instruction }\n"

        regs = self._regfile.canonical_registers
        for reg_name in regs:
            value = self.read_register(reg_name)
            if issymbolic(value):
                aux = "%3s: "%reg_name +"%16s"%value
                result += aux
            elif isinstance(value, (int, long)):
                result += "%3s: 0x%016x"%(reg_name, value)
            else:
                result += "%3s: %r"%(reg_name, value)
            pos = 0
            result += '\n'

        return result


class DecodeException(Exception):
    ''' You tried to decode an unknown or invalid intruction '''
    def __init__(self, pc, bytes, extra):
        super(DecodeException, self).__init__("Error decoding instruction @%08x", pc)
        self.pc=pc
        self.bytes=bytes
        self.extra=extra

class InvalidPCException(Exception):
    ''' Exception raised when you try to execute invalid or not executable memory
    '''
    def __init__(self, pc):
        super(InvalidPCException, self).__init__("Trying to execute invalid memory @%08x"%pc)
        self.pc=pc

class InstructionNotImplementedError(Exception):
    ''' Exception raised when you try to execute an instruction that is
        not yet implemented in the emulator.
        Go to cpu.py and add it!
    '''
    pass

class DivideError(Exception):
    ''' A division by zero '''
    pass

class CpuInterrupt(Exception):
    ''' Any interruption triggred by the CPU '''
    pass

class Interruption(CpuInterrupt):
    ''' '''
    def __init__(self, N):
        super(Interruption,self).__init__("CPU Software Interruption %08x", N)
        self.N = N

class Syscall(CpuInterrupt):
    ''' '''
    def __init__(self):
        super(Syscall, self).__init__("CPU Syscall")

class ConcretizeRegister(Exception):
    ''' '''
    def __init__(self, reg_name, message, policy='MINMAX'):
        assert policy in ['MINMAX', 'ALL', 'SAMPLED']
        super(ConcretizeRegister, self).__init__("Concretizing %s (%s). %s"%(reg_name, policy, message))
        self.reg_name = reg_name
        self.policy = policy

class ConcretizeMemory(Exception):
    ''' '''
    def __init__(self, address, size, message, policy='MINMAX'):
        assert policy in ['MINMAX', 'ALL', 'SAMPLED']
        super(ConcretizeMemory, self).__init__("Concretizing byte at %x (%s). %s"%(address, policy, message))
        self.address = address
        self.size = size
        self.policy = policy

class ConcretizeArgument(Exception):
    ''' '''
    def __init__(self, argnum, policy='MINMAX'):
        assert policy in ['MINMAX', 'ALL', 'SAMPLED']
        super(ConcretizeArgument, self).__init__("Concretizing argument #%d (%s): "%(argnum, policy))
        self.argnum = argnum
        self.policy = policy


class SymbolicPCException(ConcretizeRegister):
    ''' '''
    def __init__(self):
        super(SymbolicPCException, self).__init__("PC", "Symbolic PC", "ALL")

class IgnoreAPI(Exception):
    def __init__(self, name):
        super(IgnoreAPI, self).__init__("Ignoring API: {}".format(name))
        self.name = name

class Sysenter(CpuInterrupt):
    ''' '''
    def __init__(self):
        super(Sysenter, self).__init__("CPU Sysenter")


#Instruction decorators
def instruction(old_method):
    #This should decorate every instruction implementation
    @wraps(old_method)
    def new_method(cpu, *args, **kw_args):
        cpu.PC += cpu.instruction.size
        return old_method(cpu,*args,**kw_args)
    new_method.old_method=old_method
    return new_method
