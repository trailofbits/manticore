import inspect
import logging
import StringIO
import sys
import types

from functools import wraps
from itertools import islice, imap

import capstone as cs

from .disasm import init_disassembler
from ..smtlib import Expression, Bool, BitVec, Array, Operators, Constant
from ..memory import (
    ConcretizeMemory, InvalidMemoryAccess, MemoryException, FileMap, AnonMap
)
from ...utils.helpers import issymbolic
from ...utils.emulate import UnicornEmulator
from ...utils.event import Eventful

logger = logging.getLogger("CPU")
register_logger = logging.getLogger("REGISTERS")

###################################################################################
#Exceptions
class CpuException(Exception):
    ''' Base cpu exception '''
    pass

class DecodeException(CpuException):
    '''
    Raised when trying to decode an unknown or invalid instruction '''
    def __init__(self, pc, bytes):
        super(DecodeException, self).__init__("Error decoding instruction @%08x", pc)
        self.pc=pc
        self.bytes=bytes

class InstructionNotImplementedError(CpuException):
    '''
    Exception raised when you try to execute an instruction that is not yet
    implemented in the emulator. Add it to the Cpu-specific implementation.
    '''
    pass

class DivideByZeroError(CpuException):
    ''' A division by zero '''
    pass

class Interruption(CpuException):
    ''' A software interrupt. '''
    def __init__(self, N):
        super(Interruption,self).__init__("CPU Software Interruption %08x", N)
        self.N = N

class Syscall(CpuException):
    ''' '''
    def __init__(self):
        super(Syscall, self).__init__("CPU Syscall")


class ConcretizeRegister(CpuException):
    '''
    Raised when a symbolic register needs to be concretized.
    '''
    def __init__(self, cpu, reg_name, message=None, policy='MINMAX'):
        self.message = message if message else "Concretizing {}".format(reg_name)

        self.cpu = cpu
        self.reg_name = reg_name
        self.policy = policy

class ConcretizeArgument(CpuException):
    '''
    Raised when a symbolic argument needs to be concretized.
    '''
    def __init__(self, cpu, argnum, policy='MINMAX'):
        self.message = "Concretizing argument #%d."%(argnum,)
        self.cpu = cpu
        self.policy = policy
        self.argnum = argnum


SANE_SIZES = {8, 16, 32, 64, 80, 128, 256}
class Operand(object):
    """This class encapsulates how to access operands (regs/mem/immediates) for
    different CPUs
    """
    class MemSpec(object):
        '''
        Auxiliary class wraps capstone operand 'mem' attribute. This will
        return register names instead of Ids
        '''
        def __init__(self, parent):
            self.parent = parent
        segment = property(lambda self: self.parent._reg_name(self.parent.op.mem.segment))
        base = property(lambda self: self.parent._reg_name(self.parent.op.mem.base))
        index = property(lambda self: self.parent._reg_name(self.parent.op.mem.index))
        scale = property(lambda self: self.parent.op.mem.scale)
        disp = property(lambda self: self.parent.op.mem.disp)

    def __init__(self, cpu, op):
        '''
        This encapsulates the arch-independent way to access instruction
        operands and immediates based on the dissasembler operand descriptor in
        use. This class knows how to browse an operand and get its details.

        It also knows how to access the specific Cpu to get the actual values
        from memory and registers.

        :param Cpu cpu: A Cpu instance
        :param Operand op: An wrapped Instruction Operand
        :type op: X86Op or ArmOp
        '''
        assert isinstance(cpu, Cpu)
        self.cpu = cpu
        self.op = op
        self.mem = Operand.MemSpec(self)

    def _reg_name(self, reg_id):
        '''
        Translates a register ID from the disassembler object into the
        register name based on manticore's alias in the register file

        :param int reg_id: Register ID
        '''
        cs_reg_name = self.cpu.instruction.reg_name(reg_id)
        if cs_reg_name is None or cs_reg_name.lower() == '(invalid)':
            return None
        return self.cpu._regfile._alias(cs_reg_name.upper())

    def __getattr__(self, name):
        return getattr(self.op, name)

    @property
    def type(self):
        ''' This property encapsulates the operand type.
            It may be one of the following:
                register
                memory
                immediate
        '''
        raise NotImplementedError

    @property
    def size(self):
        ''' Return bit size of operand '''
        raise NotImplementedError

    @property
    def reg(self):
        return self._reg_name(self.op.reg)

    def address(self):
        ''' On a memory operand it returns the effective address '''
        raise NotImplementedError

    def read(self):
        ''' It reads the operand value from the registers or memory '''
        raise NotImplementedError

    def write(self, value):
        ''' It writes the value of specific type to the registers or memory '''
        raise NotImplementedError

#  Basic register file structure not actually need to abstract as it's used
#  only from the cpu implementation
class RegisterFile(object):
    def __init__(self, aliases=None):
        # dict mapping from alias register name ('PC') to actual register
        # name ('RIP')
        self._aliases = aliases if aliases is not None else {}

    def _alias(self, register):
        '''
        Get register canonical alias. ex. PC->RIP or PC->R15

        :param str register: The register name
        '''
        return self._aliases.get(register, register)

    def write(self, register, value):
        '''
        Write value to the specified register

        :param str register: a register id. Must be listed on all_registers
        :param value: a value of the expected type
        :type value: int or long or Expression
        :return: the value actually written to the register
        '''
        raise NotImplementedError

    def read(self, register):
        '''
        Read value from specified register

        :param str register: a register name. Must be listed on all_registers
        :return: the register value
        '''
        raise NotImplementedError

    @property
    def all_registers(self):
        ''' Lists all possible register names (Including aliases) '''
        return tuple(self._aliases)

    @property
    def canonical_registers(self):
        ''' List the minimal most beautiful set of registers needed '''
        raise NotImplementedError

    def __contains__(self, register):
        '''
        Check for register validity

        :param register: a register name
        '''
        return self._alias(register) in self.all_registers

class Abi(object):
    '''
    Represents the ability to extract arguments from the environment and write
    back a result.

    Used for function call and system call models.
    '''
    def __init__(self, cpu):
        '''
        :param manticore.core.cpu.Cpu cpu: CPU to initialize with
        '''
        self._cpu = cpu

    def get_arguments(self):
        '''
        Extract model arguments conforming to `convention`. Produces an iterable
        of argument descriptors following the calling convention. A descriptor
        is either a string describing a register, or an address (concrete or
        symbolic).

        :return: iterable returning syscall arguments.
        :rtype: iterable
        '''
        raise NotImplementedError

    def write_result(self, result):
        '''
        Write the result of a model back to the environment.

        :param result: result of the model implementation
        '''
        raise NotImplementedError

    def ret(self):
        '''
        Handle the "ret" semantics of the ABI, i.e. reclaiming stack space,
        popping PC, etc.

        A null operation by default.
        '''
        return

    def values_from(self, base):
        '''
        A reusable generator for increasing pointer-sized values from an address
        (usually the stack).
        '''
        word_bytes = self._cpu.address_bit_size / 8
        while True:
            yield base
            base += word_bytes

    def invoke(self, model, prefix_args=None):
        '''
        Invoke a callable `model` as if it was a native function. If
        :func:`~manticore.models.isvariadic` returns true for `model`, `model` receives a single
        argument that is a generator for function arguments. Pass a tuple of
        arguments for `prefix_args` you'd like to precede the actual
        arguments.

        :param callable model: Python model of the function
        :param tuple prefix_args: Parameters to pass to model before actual ones
        :return: The result of calling `model`
        '''
        prefix_args = prefix_args or ()

        spec = inspect.getargspec(model)

        if spec.varargs:
            logger.warning("ABI: A vararg model must be a unary function.")

        nargs = len(spec.args) - len(prefix_args)

        # If the model is a method, we need to account for `self`
        if inspect.ismethod(model):
            nargs -= 1

        def resolve_argument(arg):
            if isinstance(arg, str):
                return self._cpu.read_register(arg)
            else:
                return self._cpu.read_int(arg)

        # Create a stream of resolved arguments from argument descriptors
        descriptors = self.get_arguments()
        argument_iter = imap(resolve_argument, descriptors)

        # TODO(mark) this is here as a hack to avoid circular import issues
        from ...models import isvariadic

        try:
            if isvariadic(model):
                result = model(*(prefix_args + (argument_iter,)))
            else:
                argument_tuple = prefix_args + tuple(islice(argument_iter, nargs))
                result = model(*argument_tuple)
        except ConcretizeArgument as e:
            assert e.argnum >= len(prefix_args), "Can't concretize a constant arg"
            idx = e.argnum - len(prefix_args)

            # Arguments were lazily computed in case of variadic, so recompute here
            descriptors = self.get_arguments()
            src = next(islice(descriptors, idx, idx+1))

            msg = 'Concretizing due to model invocation'
            if isinstance(src, str):
                raise ConcretizeRegister(self._cpu, src, msg)
            else:
                raise ConcretizeMemory(self._cpu.memory, src, self._cpu.address_bit_size, msg)
        else:
            if result is not None:
                self.write_result(result)

            self.ret()

        return result

class SyscallAbi(Abi):
    '''
    A system-call specific ABI.
    '''
    def syscall_number(self):
        '''
        Extract the index of the invoked syscall.

        :return: int
        '''
        raise NotImplementedError

############################################################################
# Abstract cpu encapsulating common cpu methods used by platforms and executor.
class Cpu(Eventful):
    '''
    Base class for all Cpu architectures. Functionality common to all
    architectures (and expected from users of a Cpu) should be here. Commonly
    used by platforms and py:class:manticore.core.Executor

    The following attributes need to be defined in any derived class

    - arch
    - mode
    - max_instr_width
    - address_bit_size
    - pc_alias
    - stack_alias
    '''

    def __init__(self, regfile, memory, **kwargs):
        assert isinstance(regfile, RegisterFile)
        self._disasm = kwargs.pop("disasm", 'capstone')
        super(Cpu, self).__init__(**kwargs)
        self._regfile = regfile
        self._memory = memory
        self._instruction_cache = {}
        self._icount = 0
        self._last_pc = None
        if not hasattr(self, "disasm"):
            self.disasm = init_disassembler(self._disasm, self.arch, self.mode)
        # Ensure that regfile created STACK/PC aliases
        assert 'STACK' in self._regfile
        assert 'PC' in self._regfile

    def __getstate__(self):
        state = super(Cpu, self).__getstate__()
        state['regfile'] = self._regfile
        state['memory'] = self._memory
        state['icount'] = self._icount
        state['last_pc'] = self._last_pc
        state['disassembler'] = self._disasm
        return state

    def __setstate__(self, state):
        Cpu.__init__(self, state['regfile'],
                     state['memory'],
                     disasm=state['disassembler'])
        self._icount = state['icount']
        self._last_pc = state['last_pc']
        self._disasm = state['disassembler']
        super(Cpu, self).__setstate__(state)

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
        '''
        Returns all register names for this CPU. Any register returned can be
        accessed via a `cpu.REG` convenience interface (e.g. `cpu.EAX`) for both
        reading and writing.

        :return: valid register names
        :rtype: tuple[str]
        '''
        return self._regfile.all_registers

    @property
    def canonical_registers(self):
        '''
        Returns the list of all register names  for this CPU.

        :rtype: tuple
        :return: the list of register names for this CPU.
        '''
        return self._regfile.canonical_registers

    def write_register(self, register, value):
        '''
        Dynamic interface for writing cpu registers

        :param str register: register name (as listed in `self.all_registers`)
        :param value: register value
        :type value: int or long or Expression
        '''
        self.publish('will_write_register', register, value)
        value = self._regfile.write(register, value)
        self.publish('did_write_register', register, value)
        return value

    def read_register(self, register):
        '''
        Dynamic interface for reading cpu registers

        :param str register: register name (as listed in `self.all_registers`)
        :return: register value
        :rtype: int or long or Expression
        '''
        self.publish('will_read_register', register)
        value = self._regfile.read(register)
        self.publish('did_read_register', register, value)
        return value

    # Pythonic access to registers and aliases
    def __getattr__(self, name):
        '''
        A Pythonic version of read_register

        :param str name: Name of the register
        '''
        assert name != '_regfile'
        if hasattr(self, '_regfile') and name in self._regfile:
            return self.read_register(name)
        raise AttributeError(name)

    def __setattr__(self, name, value):
        '''
        A Pythonic version of write_register

        :param str name: Name of the register to set
        :param value: The value to set the register to
        :type param: int or long or Expression
        '''
        if hasattr(self, '_regfile') and name in self._regfile:
            return self.write_register(name, value)
        object.__setattr__(self, name, value)


    #############################
    # Memory access
    @property
    def memory(self):
        return self._memory

    def write_int(self, where, expression, size=None):
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
        self.publish('will_write_memory', where, expression, size)

        self.memory[where:where+size/8] = [Operators.CHR(Operators.EXTRACT(expression, offset, 8)) for offset in xrange(0, size, 8)]

        self.publish('did_write_memory', where, expression, size)


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
        self.publish('will_read_memory', where, size)

        data = self.memory[where:where + size / 8]
        assert (8 * len(data)) == size
        value = Operators.CONCAT(size, *map(Operators.ORD, reversed(data)))

        self.publish('did_read_memory', where, value, size)
        return value


    def write_bytes(self, where, data):
        '''
        Write a concrete or symbolic (or mixed) buffer to memory

        :param int where: address to write to
        :param data: data to write
        :type data: str or list
        '''
        for i in xrange(len(data)):
            self.write_int(where + i, Operators.ORD(data[i]), 8)

    def read_bytes(self, where, size):
        '''
        Read from memory.

        :param int where: address to read data from
        :param int size: number of bytes
        :return: data
        :rtype: list[int or Expression]
        '''
        result = []
        for i in xrange(size):
            result.append(Operators.CHR(self.read_int(where + i, 8)))
        return result

    def read_string(self, where, max_length=None):
        '''
        Read a NUL-terminated concrete buffer from memory.

        :param int where: Address to read string from
        :param int max_length:
            The size in bytes to cap the string at, or None [default] for no
            limit.
        :return: string read
        :rtype: str
        '''
        s = StringIO.StringIO()
        while True:
            c = self.read_int(where, 8)

            assert not issymbolic(c)

            if c == 0:
                break

            if max_length is not None:
                if max_length == 0:
                    break
                max_length = max_length - 1
            s.write(Operators.CHR(c))
            where += 1
        return s.getvalue()

    def push_bytes(self, data):
        '''
        Write `data` to the stack and decrement the stack pointer accordingly.

        :param str data: Data to write
        '''
        self.STACK -= len(data)
        self.write_bytes(self.STACK, data)
        return self.STACK

    def pop_bytes(self, nbytes):
        '''
        Read `nbytes` from the stack, increment the stack pointer, and return
        data.

        :param int nbytes: How many bytes to read
        :return: Data read from the stack
        '''
        data = self.read_bytes(self.STACK, nbytes)
        self.STACK += nbytes
        return data

    def push_int(self, value):
        '''
        Decrement the stack pointer and write `value` to the stack.

        :param int value: The value to write
        :return: New stack pointer
        '''
        self.STACK -= self.address_bit_size / 8
        self.write_int(self.STACK, value)
        return self.STACK

    def pop_int(self):
        '''
        Read a value from the stack and increment the stack pointer.

        :return: Value read
        '''
        value = self.read_int(self.STACK)
        self.STACK += self.address_bit_size / 8
        return value


    #######################################
    # Decoder
    def _wrap_operands(self, operands):
        '''
        Private method to decorate an Operand to our needs based on the
        underlying architecture.
        See :class:`~manticore.core.cpu.abstractcpu.Operand` class
        '''
        raise NotImplementedError

    def decode_instruction(self, pc):
        '''
        This will decode an instruction from memory pointed by `pc`

        :param int pc: address of the instruction
        '''
        # No dynamic code!!! #TODO!
        # Check if instruction was already decoded
        if pc in self._instruction_cache:
            return self._instruction_cache[pc]

        text = ''
        # Read Instruction from memory
        for address in xrange(pc, pc+self.max_instr_width):
            #This reads a byte from memory ignoring permissions
            #and concretize it if symbolic
            if not self.memory.access_ok(address, 'x'):
                break

            c = self.memory[address]

            if issymbolic(c):
                assert isinstance(c, BitVec) and  c.size == 8
                if isinstance(c, Constant):
                    c = chr(c.value)
                else:
                    logger.error('Concretize executable memory %r %r', c, text)
                    raise ConcretizeMemory(self.memory,
                                           address=pc,
                                           size=8 * self.max_instr_width,
                                           policy='INSTRUCTION')
            text += c


        #Pad potentially incomplete instruction with zeroes

        code = text.ljust(self.max_instr_width, '\x00')

        try:
            # decode the instruction from code
            insn = self.disasm.disassemble_instruction(code, pc)
        except StopIteration as e:
            raise DecodeException(pc, code)

        #Check that the decoded instruction is contained in executable memory
        if not self.memory.access_ok(slice(pc, pc + insn.size), 'x'):
            logger.info("Trying to execute instructions from non-executable memory")
            raise InvalidMemoryAccess(pc, 'x')

        insn.operands = self._wrap_operands(insn.operands)
        self._instruction_cache[pc] = insn
        return insn

    @property
    def instruction(self):
        if self._last_pc is None:
            return self.decode_instruction(self.PC)
        else:
            return self.decode_instruction(self._last_pc)

    #######################################
    # Execute
    def canonicalize_instruction_name(self, instruction):
        '''
        Get the semantic name of an instruction.
        '''
        raise NotImplemented

    def execute(self):
        '''
        Decode, and execute one instruction pointed by register PC
        '''
        if issymbolic(self.PC):
            raise ConcretizeRegister(self, 'PC', policy='ALL')

        if not self.memory.access_ok(self.PC, 'x'):
            raise InvalidMemoryAccess(self.PC, 'x')

        self.publish('will_decode_instruction', self.PC)

        insn = self.decode_instruction(self.PC)
        self._last_pc = self.PC

        self.publish('will_execute_instruction', insn)

        # FIXME (theo) why just return here?
        if insn.address != self.PC:
            return

        if logger.level == logging.DEBUG :
            logger.debug(self.render_instruction(insn))
            for l in self.render_registers():
                register_logger.debug(l)

        self._insn_implementation(insn)
        self._icount += 1
        self.publish('did_execute_instruction', instruction)

    def fallback_to_emulate(self, *operands):
        insn = self.instruction
        text_bytes = ' '.join('%02x'%x for x in insn.bytes)
        logger.info("Unimplemented instruction: 0x%016x:\t%s\t%s\t%s",
                insn.address, text_bytes, insn.mnemonic, insn.op_str)

        self.publish('will_emulate_instruction', insn)
        self.emulate(insn)

        self.publish('did_emulate_instruction', insn)

    def _insn_implementation(self, insn):
        name = self.canonicalize_instruction_name(insn)

        implementation = getattr(self, name, self.fallback_to_emulate)
        implementation(*insn.operands)
        self.update_pc()

    # to be overriden if needed
    def update_pc(self):
        pass

    def emulate(self, insn):
        '''
        If we could not handle emulating an instruction, use Unicorn to emulate
        it.

        :param capstone.CsInsn instruction: The instruction object to emulate
        '''

        emu = UnicornEmulator(self)
        emu.emulate(insn)


        # We have been seeing occasional Unicorn issues with it not clearing
        # the backing unicorn instance. Saw fewer issues with the following
        # line present.
        del emu

    def render_instruction(self, insn=None):
        try:
            insn = self.instruction
            return "INSTRUCTION: 0x%016x:\t%s\t%s" % (insn.address,
                                                      insn.mnemonic,
                                                      insn.op_str)
        except Exception as e:
            return "{can't decode instruction}"

    def render_register(self, reg_name):
        result = ""

        value = self.read_register(reg_name)

        if issymbolic(value):
            aux = "%3s: "%reg_name +"%16s"%value
            result += aux
        elif isinstance(value, (int, long)):
            result += "%3s: 0x%016x" % (reg_name, value)
        else:
            result += "%3s: %r" % (reg_name, value)
        return result

    def render_registers(self):
        # FIXME add a context manager at utils that look for all Signal
        # backup, null, use, then restore the list.
        # will disabled_signals(self):
        #    return map(self.render_register, self._regfile.canonical_registers)
        return map(self.render_register,
                   sorted(self._regfile.canonical_registers))

    #Generic string representation
    def __str__(self):
        '''
        Returns a string representation of cpu state

        :rtype: str
        :return: name and current value for all the registers.
        '''
        result = self.render_instruction() + "\n"
        result += '\n'.join(self.render_registers())
        return result

#Instruction decorators
def instruction(old_method):
    #This should decorate every instruction implementation
    @wraps(old_method)
    def new_method(cpu, *args, **kw_args):
        cpu.PC += cpu.instruction.size
        return old_method(cpu, *args, **kw_args)
    new_method.old_method = old_method
    return new_method
