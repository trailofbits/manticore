import inspect
import logging
import StringIO
import string

from functools import wraps
from itertools import islice, imap

import capstone as cs
import unicorn

from .disasm import init_disassembler
from ..smtlib import Expression, Bool, BitVec, Array, Operators, Constant
from ..memory import (
    ConcretizeMemory, InvalidMemoryAccess, MemoryException, FileMap, AnonMap
)
from ...utils.helpers import issymbolic
from ...utils.emulate import UnicornEmulator
from ...utils.event import Eventful

logger = logging.getLogger(__name__)
register_logger = logging.getLogger('{}.registers'.format(__name__))

###################################################################################
# Exceptions


class CpuException(Exception):
    ''' Base cpu exception '''

class DecodeException(CpuException):
    '''
    Raised when trying to decode an unknown or invalid instruction '''

    def __init__(self, pc, bytes):
        super(DecodeException, self).__init__("Error decoding instruction @%08x", pc)
        self.pc = pc
        self.bytes = bytes


class InstructionNotImplementedError(CpuException):
    '''
    Exception raised when you try to execute an instruction that is not yet
    implemented in the emulator. Add it to the Cpu-specific implementation.
    '''


class InstructionEmulationError(CpuException):
    '''
    Exception raised when failing to emulate an instruction outside of Manticore.
    '''


class DivideByZeroError(CpuException):
    ''' A division by zero '''


class Interruption(CpuException):
    ''' A software interrupt. '''

    def __init__(self, N):
        super(Interruption, self).__init__("CPU Software Interruption %08x", N)
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
        self.message = "Concretizing argument #%d." % (argnum,)
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

    def get_argument_values(self, model, prefix_args):
        '''
        Extract arguments for model from the environment and return as a tuple that
        is ready to be passed to the model.

        :param callable model: Python model of the function
        :param tuple prefix_args: Parameters to pass to model before actual ones
        :return: Arguments to be passed to the model
        :rtype: tuple
        '''
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

        if isvariadic(model):
            arguments = prefix_args + (argument_iter,)
        else:
            arguments = prefix_args + tuple(islice(argument_iter, nargs))

        return arguments

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

        arguments = self.get_argument_values(model, prefix_args)

        try:
            result = model(*arguments)
        except ConcretizeArgument as e:
            assert e.argnum >= len(prefix_args), "Can't concretize a constant arg"
            idx = e.argnum - len(prefix_args)

            # Arguments were lazily computed in case of variadic, so recompute here
            descriptors = self.get_arguments()
            src = next(islice(descriptors, idx, idx + 1))

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


platform_logger = logging.getLogger('manticore.platforms.platform')


class SyscallAbi(Abi):
    '''
    A system-call specific ABI.

    Captures model arguments and return values for centralized logging.
    '''

    def syscall_number(self):
        '''
        Extract the index of the invoked syscall.

        :return: int
        '''
        raise NotImplementedError

    def get_argument_values(self, model, prefix_args):
        self._last_arguments = super(SyscallAbi, self).get_argument_values(model, prefix_args)
        return self._last_arguments

    def invoke(self, model, prefix_args=None):
        # invoke() will call get_argument_values()
        self._last_arguments = ()

        ret = super(SyscallAbi, self).invoke(model, prefix_args)

        if platform_logger.isEnabledFor(logging.DEBUG):
            # Try to expand strings up to max_arg_expansion
            max_arg_expansion = 32
            # Add a hex representation to return if greater than min_hex_expansion
            min_hex_expansion = 0x80

            args = []
            for arg in self._last_arguments:
                arg_s = "0x{:x}".format(arg)
                if self._cpu.memory.access_ok(arg, 'r'):
                    s = self._cpu.read_string(arg, max_arg_expansion)
                    if all(c in string.printable for c in s):
                        if len(s) == max_arg_expansion:
                            s = s + '..'
                        if len(s) > 2:
                            arg_s = arg_s + ' ({})'.format(s.translate(None, '\n'))
                args.append(arg_s)

            args_s = ', '.join(args)

            ret_s = '{}'.format(ret)
            if ret > min_hex_expansion:
                ret_s = ret_s + '(0x{:x})'.format(ret)

            platform_logger.debug('%s(%s) -> %s', model.im_func.func_name, args_s, ret_s)

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

    _published_events = {'write_register', 'read_register', 'write_memory', 'read_memory', 'decode_instruction',
                         'execute_instruction'}

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
        self._publish('will_write_register', register, value)
        value = self._regfile.write(register, value)
        self._publish('did_write_register', register, value)
        return value

    def read_register(self, register):
        '''
        Dynamic interface for reading cpu registers

        :param str register: register name (as listed in `self.all_registers`)
        :return: register value
        :rtype: int or long or Expression
        '''
        self._publish('will_read_register', register)
        value = self._regfile.read(register)
        self._publish('did_read_register', register, value)
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

    def write_int(self, where, expression, size=None, force=False):
        '''
        Writes int to memory

        :param int where: address to write to
        :param expr: value to write
        :type expr: int or BitVec
        :param size: bit size of `expr`
        :param force: whether to ignore memory permissions
        '''
        if size is None:
            size = self.address_bit_size
        assert size in SANE_SIZES
        self._publish('will_write_memory', where, expression, size)

        data = [Operators.CHR(Operators.EXTRACT(expression, offset, 8)) for offset in xrange(0, size, 8)]
        self._memory.write(where, data, force)

        self._publish('did_write_memory', where, expression, size)

    def read_int(self, where, size=None, force=False):
        '''
        Reads int from memory

        :param int where: address to read from
        :param size: number of bits to read
        :return: the value read
        :rtype: int or BitVec
        :param force: whether to ignore memory permissions
        '''
        if size is None:
            size = self.address_bit_size
        assert size in SANE_SIZES
        self._publish('will_read_memory', where, size)

        data = self._memory.read(where, size / 8, force)
        assert (8 * len(data)) == size
        value = Operators.CONCAT(size, *map(Operators.ORD, reversed(data)))

        self._publish('did_read_memory', where, value, size)
        return value

    def write_bytes(self, where, data, force=False):
        '''
        Write a concrete or symbolic (or mixed) buffer to memory

        :param int where: address to write to
        :param data: data to write
        :type data: str or list
        :param force: whether to ignore memory permissions
        '''
        for i in xrange(len(data)):
            self.write_int(where + i, Operators.ORD(data[i]), 8, force)

    def read_bytes(self, where, size, force=False):
        '''
        Read from memory.

        :param int where: address to read data from
        :param int size: number of bytes
        :param force: whether to ignore memory permissions
        :return: data
        :rtype: list[int or Expression]
        '''
        result = []
        for i in xrange(size):
            result.append(Operators.CHR(self.read_int(where + i, 8, force)))
        return result

    def write_string(self, where, string, max_length=None, force=False):
        '''
        Writes a string to memory, appending a NULL-terminator at the end.
        :param int where: Address to write the string to
        :param str string: The string to write to memory
        :param int max_length:
            The size in bytes to cap the string at, or None [default] for no
            limit. This includes the NULL terminator.
        :param force: whether to ignore memory permissions
        '''

        if max_length is not None:
            string = string[:max_length - 1]

        self.write_bytes(where, string + '\x00', force)

    def read_string(self, where, max_length=None, force=False):
        '''
        Read a NUL-terminated concrete buffer from memory. Stops reading at first symbolic byte.

        :param int where: Address to read string from
        :param int max_length:
            The size in bytes to cap the string at, or None [default] for no
            limit.
        :param force: whether to ignore memory permissions
        :return: string read
        :rtype: str
        '''
        s = StringIO.StringIO()
        while True:
            c = self.read_int(where, 8, force)

            if issymbolic(c) or c == 0:
                break

            if max_length is not None:
                if max_length == 0:
                    break
                max_length = max_length - 1
            s.write(Operators.CHR(c))
            where += 1
        return s.getvalue()

    def push_bytes(self, data, force=False):
        '''
        Write `data` to the stack and decrement the stack pointer accordingly.

        :param str data: Data to write
        :param force: whether to ignore memory permissions
        '''
        self.STACK -= len(data)
        self.write_bytes(self.STACK, data, force)
        return self.STACK

    def pop_bytes(self, nbytes, force=False):
        '''
        Read `nbytes` from the stack, increment the stack pointer, and return
        data.

        :param int nbytes: How many bytes to read
        :param force: whether to ignore memory permissions
        :return: Data read from the stack
        '''
        data = self.read_bytes(self.STACK, nbytes, force=force)
        self.STACK += nbytes
        return data

    def push_int(self, value, force=False):
        '''
        Decrement the stack pointer and write `value` to the stack.

        :param int value: The value to write
        :param force: whether to ignore memory permissions
        :return: New stack pointer
        '''
        self.STACK -= self.address_bit_size / 8
        self.write_int(self.STACK, value, force=force)
        return self.STACK

    def pop_int(self, force=False):
        '''
        Read a value from the stack and increment the stack pointer.

        :param force: whether to ignore memory permissions
        :return: Value read
        '''
        value = self.read_int(self.STACK, force=force)
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
        for address in xrange(pc, pc + self.max_instr_width):
            # This reads a byte from memory ignoring permissions
            # and concretize it if symbolic
            if not self.memory.access_ok(address, 'x'):
                break

            c = self.memory[address]

            if issymbolic(c):
                assert isinstance(c, BitVec) and c.size == 8
                if isinstance(c, Constant):
                    c = chr(c.value)
                else:
                    logger.error('Concretize executable memory %r %r', c, text)
                    raise ConcretizeMemory(self.memory,
                                           address=pc,
                                           size=8 * self.max_instr_width,
                                           policy='INSTRUCTION')
            text += c

        # Pad potentially incomplete instruction with zeroes

        code = text.ljust(self.max_instr_width, '\x00')

        try:
            # decode the instruction from code
            insn = self.disasm.disassemble_instruction(code, pc)
        except StopIteration as e:
            raise DecodeException(pc, code)

        # Check that the decoded instruction is contained in executable memory
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

        self._publish('will_decode_instruction', self.PC)

        insn = self.decode_instruction(self.PC)
        self._last_pc = self.PC

        self._publish('will_execute_instruction', self.PC, insn)

        # FIXME (theo) why just return here?
        if insn.address != self.PC:
            return

        name = self.canonicalize_instruction_name(insn)

        if logger.level == logging.DEBUG:
            logger.debug(self.render_instruction(insn))
            for l in self.render_registers():
                register_logger.debug(l)

        try:
            implementation = getattr(self, name, None)

            if implementation is not None:
                implementation(*insn.operands)

            else:
                text_bytes = ' '.join('%02x' % x for x in insn.bytes)
                logger.info("Unimplemented instruction: 0x%016x:\t%s\t%s\t%s",
                            insn.address, text_bytes, insn.mnemonic, insn.op_str)
                self.emulate(insn)

        except (Interruption, Syscall) as e:
            e.on_handled = lambda: self._publish_instruction_as_executed(insn)
            raise e
        else:
            self._publish_instruction_as_executed(insn)

    # FIXME(yan): In the case the instruction implementation invokes a system call, we would not be able to
    # publish the did_execute_instruction event from here, so we capture and attach it to the syscall
    # exception for the platform to emit it for us once the syscall has successfully been executed.
    def _publish_instruction_as_executed(self, insn):
        '''
        Notify listeners that an instruction has been executed.
        '''
        self._icount += 1
        self._publish('did_execute_instruction', self._last_pc, self.PC, insn)

    def emulate(self, insn):
        '''
        If we could not handle emulating an instruction, use Unicorn to emulate
        it.

        :param capstone.CsInsn instruction: The instruction object to emulate
        '''

        emu = UnicornEmulator(self)
        try:
            emu.emulate(insn)
        except unicorn.UcError as e:
            if e.errno == unicorn.UC_ERR_INSN_INVALID:
                text_bytes = ' '.join('%02x' % x for x in insn.bytes)
                logger.error("Unimplemented instruction: 0x%016x:\t%s\t%s\t%s",
                             insn.address, text_bytes, insn.mnemonic, insn.op_str)
            raise InstructionEmulationError(str(e))
        finally:
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
            aux = "%3s: " % reg_name + "%16s" % value
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

    # Generic string representation
    def __str__(self):
        '''
        Returns a string representation of cpu state

        :rtype: str
        :return: name and current value for all the registers.
        '''
        result = self.render_instruction() + "\n"
        result += '\n'.join(self.render_registers())
        return result

# Instruction decorators


def instruction(old_method):
    # This should decorate every instruction implementation
    @wraps(old_method)
    def new_method(cpu, *args, **kw_args):
        cpu.PC += cpu.instruction.size
        return old_method(cpu, *args, **kw_args)
    new_method.old_method = old_method
    return new_method
