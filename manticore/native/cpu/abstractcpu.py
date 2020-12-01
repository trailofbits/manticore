import inspect
import io
import logging
import struct
import types
from functools import wraps, partial
from itertools import islice

import unicorn

from .disasm import init_disassembler
from ..memory import ConcretizeMemory, InvalidMemoryAccess, FileMap, AnonMap
from ..memory import LazySMemory, Memory
from ...core.smtlib import Operators, Constant, issymbolic
from ...core.smtlib import visitors
from ...core.smtlib.solver import SelectedSolver
from ...utils.emulate import ConcreteUnicornEmulator
from ...utils.event import Eventful
from ...utils.fallback_emulator import UnicornEmulator

from capstone import CS_ARCH_ARM64, CS_ARCH_X86, CS_ARCH_ARM
from capstone.arm64 import ARM64_REG_ENDING
from capstone.x86 import X86_REG_ENDING
from capstone.arm import ARM_REG_ENDING

from typing import Any, Callable, Dict, Optional, Tuple

logger = logging.getLogger(__name__)
register_logger = logging.getLogger(f"{__name__}.registers")


def _sig_is_varargs(sig: inspect.Signature) -> bool:
    VAR_POSITIONAL = inspect.Parameter.VAR_POSITIONAL
    return any(p.kind == VAR_POSITIONAL for p in sig.parameters.values())


###################################################################################
# Exceptions


class CpuException(Exception):
    """ Base cpu exception """


class DecodeException(CpuException):
    """
    Raised when trying to decode an unknown or invalid instruction"""

    def __init__(self, pc, bytes):
        super().__init__("Error decoding instruction @ 0x{:x}".format(pc))
        self.pc = pc
        self.bytes = bytes


class InstructionNotImplementedError(CpuException):
    """
    Exception raised when you try to execute an instruction that is not yet
    implemented in the emulator. Add it to the Cpu-specific implementation.
    """


class InstructionEmulationError(CpuException):
    """
    Exception raised when failing to emulate an instruction outside of Manticore.
    """


class DivideByZeroError(CpuException):
    """ A division by zero """


class Interruption(CpuException):
    """ A software interrupt. """

    def __init__(self, N):
        super().__init__("CPU Software Interruption %08x" % N)
        self.N = N


class Syscall(CpuException):
    """ """

    def __init__(self):
        super().__init__("CPU Syscall")


class ConcretizeRegister(CpuException):
    """
    Raised when a symbolic register needs to be concretized.
    """

    def __init__(
        self,
        cpu: "Cpu",
        reg_name: str,
        message: Optional[str] = None,
        policy: str = "MINMAX",
    ):
        self.message = message if message else f"Concretizing {reg_name}"

        self.cpu = cpu
        self.reg_name = reg_name
        self.policy = policy


class ConcretizeArgument(CpuException):
    """
    Raised when a symbolic argument needs to be concretized.
    """

    def __init__(self, cpu, argnum, policy="MINMAX"):
        self.message = f"Concretizing argument #{argnum}."
        self.cpu = cpu
        self.policy = policy
        self.argnum = argnum


SANE_SIZES = {8, 16, 32, 64, 80, 128, 256}


class Operand:
    """This class encapsulates how to access operands (regs/mem/immediates) for
    different CPUs
    """

    class MemSpec:
        """
        Auxiliary class wraps capstone operand 'mem' attribute. This will
        return register names instead of Ids
        """

        def __init__(self, parent):
            self.parent = parent

        segment = property(lambda self: self.parent._reg_name(self.parent.op.mem.segment))
        base = property(lambda self: self.parent._reg_name(self.parent.op.mem.base))
        index = property(lambda self: self.parent._reg_name(self.parent.op.mem.index))
        scale = property(lambda self: self.parent.op.mem.scale)
        disp = property(lambda self: self.parent.op.mem.disp)

    def __init__(self, cpu: "Cpu", op):
        """
        This encapsulates the arch-independent way to access instruction
        operands and immediates based on the disassembler operand descriptor in
        use. This class knows how to browse an operand and get its details.

        It also knows how to access the specific Cpu to get the actual values
        from memory and registers.

        :param Cpu cpu: A Cpu instance
        :param Operand op: An wrapped Instruction Operand
        :type op: X86Op or ArmOp
        """
        assert isinstance(cpu, Cpu)
        self.cpu = cpu
        self.op = op
        self.mem = Operand.MemSpec(self)

    def _reg_name(self, reg_id: int):
        """
        Translates a register ID from the disassembler object into the
        register name based on manticore's alias in the register file

        :param reg_id: Register ID
        """
        # XXX: Support other architectures.
        if (
            (self.cpu.arch == CS_ARCH_ARM64 and reg_id >= ARM64_REG_ENDING)
            or (self.cpu.arch == CS_ARCH_X86 and reg_id >= X86_REG_ENDING)
            or (self.cpu.arch == CS_ARCH_ARM and reg_id >= ARM_REG_ENDING)
        ):
            logger.warning("Trying to get register name for a non-register")
            return None
        cs_reg_name = self.cpu.instruction.reg_name(reg_id)
        if cs_reg_name is None or cs_reg_name.lower() == "(invalid)":
            return None
        return self.cpu._regfile._alias(cs_reg_name.upper())

    def __getattr__(self, name):
        return getattr(self.op, name)

    @property
    def type(self):
        """This property encapsulates the operand type.
        It may be one of the following:
            register
            memory
            immediate
        """
        raise NotImplementedError

    @property
    def size(self):
        """ Return bit size of operand """
        raise NotImplementedError

    @property
    def reg(self):
        return self._reg_name(self.op.reg)

    def address(self):
        """ On a memory operand it returns the effective address """
        raise NotImplementedError

    def read(self):
        """ It reads the operand value from the registers or memory """
        raise NotImplementedError

    def write(self, value):
        """ It writes the value of specific type to the registers or memory """
        raise NotImplementedError


#  Basic register file structure not actually need to abstract as it's used
#  only from the cpu implementation


class RegisterFile:
    def __init__(self, aliases=None):
        # dict mapping from alias register name ('PC') to actual register
        # name ('RIP')
        self._aliases = aliases if aliases is not None else {}

    def _alias(self, register):
        """
        Get register canonical alias. ex. PC->RIP or PC->R15

        :param str register: The register name
        """
        return self._aliases.get(register, register)

    def write(self, register, value):
        """
        Write value to the specified register

        :param str register: a register id. Must be listed on all_registers
        :param value: a value of the expected type
        :type value: int or long or Expression
        :return: the value actually written to the register
        """
        raise NotImplementedError

    def read(self, register):
        """
        Read value from specified register

        :param str register: a register name. Must be listed on all_registers
        :return: the register value
        """
        raise NotImplementedError

    @property
    def all_registers(self):
        """ Lists all possible register names (Including aliases) """
        return tuple(self._aliases)

    @property
    def canonical_registers(self):
        """ List the minimal most beautiful set of registers needed """
        raise NotImplementedError

    def __contains__(self, register):
        """
        Check for register validity

        :param register: a register name
        """
        return self._alias(register) in self.all_registers


class Abi:
    """
    Represents the ability to extract arguments from the environment and write
    back a result.

    Used for function call and system call models.
    """

    def __init__(self, cpu: "Cpu"):
        """
        :param CPU to initialize with
        """
        self._cpu = cpu

    def get_arguments(self):
        """
        Extract model arguments conforming to `convention`. Produces an iterable
        of argument descriptors following the calling convention. A descriptor
        is either a string describing a register, or an address (concrete or
        symbolic).

        :return: iterable returning syscall arguments.
        :rtype: iterable
        """
        raise NotImplementedError

    def write_result(self, result):
        """
        Write the result of a model back to the environment.

        :param result: result of the model implementation
        """
        raise NotImplementedError

    def ret(self):
        """
        Handle the "ret" semantics of the ABI, i.e. reclaiming stack space,
        popping PC, etc.

        A null operation by default.
        """
        return

    def values_from(self, base):
        """
        A reusable generator for increasing pointer-sized values from an address
        (usually the stack).
        """
        word_bytes = self._cpu.address_bit_size // 8
        while True:
            yield base
            base += word_bytes

    def get_argument_values(self, model: Callable, prefix_args: Tuple) -> Tuple:
        """
        Extract arguments for model from the environment and return as a tuple that
        is ready to be passed to the model.

        :param model: Python model of the function
        :param prefix_args: Parameters to pass to model before actual ones
        :return: Arguments to be passed to the model
        """
        if type(model) is partial:
            # mypy issue with partial types https://github.com/python/mypy/issues/1484
            model = model.args[0]  # type: ignore
        sig = inspect.signature(model)
        if _sig_is_varargs(sig):
            model_name = getattr(model, "__qualname__", "<no name>")
            logger.warning("ABI: %s: a vararg model must be a unary function.", model_name)

        nargs = len(sig.parameters) - len(prefix_args)

        def resolve_argument(arg):
            if isinstance(arg, str):
                return self._cpu.read_register(arg)
            else:
                return self._cpu.read_int(arg)

        # Create a stream of resolved arguments from argument descriptors
        descriptors = self.get_arguments()
        argument_iter = map(resolve_argument, descriptors)

        from ..models import isvariadic  # prevent circular imports

        if isvariadic(model):
            return prefix_args + (argument_iter,)
        else:
            return prefix_args + tuple(islice(argument_iter, nargs))

    def invoke(self, model, prefix_args=None):
        """
        Invoke a callable `model` as if it was a native function. If
        :func:`~manticore.models.isvariadic` returns true for `model`, `model` receives a single
        argument that is a generator for function arguments. Pass a tuple of
        arguments for `prefix_args` you'd like to precede the actual
        arguments.

        :param callable model: Python model of the function
        :param tuple prefix_args: Parameters to pass to model before actual ones
        :return: The result of calling `model`
        """
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

            msg = "Concretizing due to model invocation"
            if isinstance(src, str):
                raise ConcretizeRegister(self._cpu, src, msg)
            else:
                raise ConcretizeMemory(self._cpu.memory, src, self._cpu.address_bit_size, msg)
        else:
            if result is not None:
                self.write_result(result)

            self.ret()

        return result


platform_logger = logging.getLogger("manticore.platforms.platform")


def unsigned_hexlify(i: Any) -> Any:
    if type(i) is int:
        if i < 0:
            return hex((1 << 64) + i)
        return hex(i)
    return i


class SyscallAbi(Abi):
    """
    A system-call specific ABI.

    Captures model arguments and return values for centralized logging.
    """

    def syscall_number(self):
        """
        Extract the index of the invoked syscall.

        :return: int
        """
        raise NotImplementedError

    def get_argument_values(self, model, prefix_args):
        self._last_arguments = super().get_argument_values(model, prefix_args)
        return self._last_arguments

    def invoke(self, model, prefix_args=None):
        # invoke() will call get_argument_values()
        self._last_arguments = ()

        if type(model) is partial:
            self._cpu._publish("will_execute_syscall", model.args[0])
        else:
            self._cpu._publish("will_execute_syscall", model)
        ret = super().invoke(model, prefix_args)
        if type(model) is partial:
            model = model.args[0]
        self._cpu._publish(
            "did_execute_syscall",
            model.__func__.__name__ if isinstance(model, types.MethodType) else model.__name__,
            self._last_arguments,
            ret,
        )

        if platform_logger.isEnabledFor(logging.DEBUG):
            # Try to expand strings up to max_arg_expansion
            max_arg_expansion = 32
            # Add a hex representation to return if greater than min_hex_expansion
            min_hex_expansion = 0x80

            args = []
            for arg in self._last_arguments:
                arg_s = (
                    unsigned_hexlify(arg)
                    if not issymbolic(arg) and abs(arg) > min_hex_expansion
                    else f"{arg}"
                )
                if self._cpu.memory.access_ok(arg, "r") and model.__func__.__name__ not in {
                    "sys_mprotect",
                    "sys_mmap",
                }:
                    try:
                        s = self._cpu.read_string(arg, max_arg_expansion)
                        s = s.rstrip().replace("\n", "\\n") if s else s
                        arg_s = f'"{s}"' if s else arg_s
                    except Exception:
                        pass
                args.append(arg_s)

            args_s = ", ".join(args)
            ret_s = f"{unsigned_hexlify(ret)}" if abs(ret) > min_hex_expansion else f"{ret}"

            platform_logger.debug("%s(%s) = %s", model.__func__.__name__, args_s, ret_s)


############################################################################
# Abstract cpu encapsulating common cpu methods used by platforms and executor.


class Cpu(Eventful):
    """
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
    """

    _published_events = {
        "write_register",
        "read_register",
        "write_memory",
        "read_memory",
        "decode_instruction",
        "execute_instruction",
        "set_descriptor",
        "map_memory",
        "protect_memory",
        "unmap_memory",
        "execute_syscall",
        "solve",
    }

    def __init__(self, regfile: RegisterFile, memory: Memory, **kwargs):
        assert isinstance(regfile, RegisterFile)
        self._disasm = kwargs.pop("disasm", "capstone")
        super().__init__(**kwargs)
        self._regfile = regfile
        self._memory = memory
        self._instruction_cache: Dict[int, Any] = {}
        self._icount = 0
        self._last_pc = None
        self._concrete = kwargs.pop("concrete", False)
        self.emu = None
        self._break_unicorn_at: Optional[int] = None
        self._delayed_event = False
        if not hasattr(self, "disasm"):
            self.disasm = init_disassembler(self._disasm, self.arch, self.mode)
        # Ensure that regfile created STACK/PC aliases
        assert "STACK" in self._regfile
        assert "PC" in self._regfile

    def __getstate__(self):
        state = super().__getstate__()
        state["regfile"] = self._regfile
        state["memory"] = self._memory
        state["icount"] = self._icount
        state["last_pc"] = self._last_pc
        state["disassembler"] = self._disasm
        state["concrete"] = self._concrete
        state["break_unicorn_at"] = self._break_unicorn_at
        state["delayed_event"] = self._delayed_event
        return state

    def __setstate__(self, state):
        Cpu.__init__(
            self,
            state["regfile"],
            state["memory"],
            disasm=state["disassembler"],
            concrete=state["concrete"],
        )
        self._icount = state["icount"]
        self._last_pc = state["last_pc"]
        self._disasm = state["disassembler"]
        self._concrete = state["concrete"]
        self._break_unicorn_at = state["break_unicorn_at"]
        self._delayed_event = state["delayed_event"]
        super().__setstate__(state)

    @property
    def icount(self):
        return self._icount

    ##############################
    # Register access
    @property
    def regfile(self):
        """ The RegisterFile of this cpu """
        return self._regfile

    @property
    def all_registers(self):
        """
        Returns all register names for this CPU. Any register returned can be
        accessed via a `cpu.REG` convenience interface (e.g. `cpu.EAX`) for both
        reading and writing.

        :return: valid register names
        :rtype: tuple[str]
        """
        return self._regfile.all_registers

    @property
    def canonical_registers(self):
        """
        Returns the list of all register names  for this CPU.

        :rtype: tuple
        :return: the list of register names for this CPU.
        """
        return self._regfile.canonical_registers

    def write_register(self, register, value):
        """
        Dynamic interface for writing cpu registers

        :param str register: register name (as listed in `self.all_registers`)
        :param value: register value
        :type value: int or long or Expression
        """
        self._publish("will_write_register", register, value)
        value = self._regfile.write(register, value)
        self._publish("did_write_register", register, value)
        return value

    def read_register(self, register):
        """
        Dynamic interface for reading cpu registers

        :param str register: register name (as listed in `self.all_registers`)
        :return: register value
        :rtype: int or long or Expression
        """
        self._publish("will_read_register", register)
        value = self._regfile.read(register)
        self._publish("did_read_register", register, value)
        return value

    # Pythonic access to registers and aliases
    def __getattr__(self, name):
        """
        A Pythonic version of read_register

        :param str name: Name of the register
        """
        if name != "_regfile":
            if name in self._regfile:
                return self.read_register(name)
        raise AttributeError(name)

    def __setattr__(self, name, value):
        """
        A Pythonic version of write_register

        :param str name: Name of the register to set
        :param value: The value to set the register to
        :type param: int or long or Expression
        """
        try:
            if name in self._regfile:
                return self.write_register(name, value)
            object.__setattr__(self, name, value)
        except AttributeError:
            object.__setattr__(self, name, value)

    def emulate_until(self, target: int):
        """
        Tells the CPU to set up a concrete unicorn emulator and use it to execute instructions
        until target is reached.

        :param target: Where Unicorn should hand control back to Manticore. Set to 0 for all instructions.
        """
        self._concrete = True
        self._break_unicorn_at = target
        if self.emu:
            self.emu._stop_at = target

    #############################
    # Memory access
    @property
    def memory(self) -> Memory:
        return self._memory

    def write_int(self, where, expression, size=None, force=False):
        """
        Writes int to memory

        :param int where: address to write to
        :param expr: value to write
        :type expr: int or BitVec
        :param size: bit size of `expr`
        :param force: whether to ignore memory permissions
        """
        if size is None:
            size = self.address_bit_size
        assert size in SANE_SIZES
        self._publish("will_write_memory", where, expression, size)

        data = [
            Operators.CHR(Operators.EXTRACT(expression, offset, 8)) for offset in range(0, size, 8)
        ]
        self._memory.write(where, data, force)

        self._publish("did_write_memory", where, expression, size)

    def _raw_read(self, where: int, size=1) -> bytes:
        """
        Selects bytes from memory. Attempts to do so faster than via read_bytes.

        :param where: address to read from
        :param size: number of bytes to read
        :return: the bytes in memory
        """
        map = self.memory.map_containing(where)
        start = map._get_offset(where)
        if isinstance(map, FileMap):
            end = map._get_offset(where + size)

            if end > map._mapped_size:
                logger.warning(
                    f"Missing {end - map._mapped_size} bytes at the end of {map._filename}"
                )

            raw_data = map._data[map._get_offset(where) : min(end, map._mapped_size)]
            if len(raw_data) < end:
                raw_data += b"\x00" * (end - len(raw_data))

            data = b""
            for offset in sorted(map._overlay.keys()):
                data += raw_data[len(data) : offset]
                data += map._overlay[offset]
            data += raw_data[len(data) :]

        elif isinstance(map, AnonMap):
            data = bytes(map._data[start : start + size])
        else:
            data = b"".join(self.memory[where : where + size])
        assert len(data) == size, "Raw read resulted in wrong data read which should never happen"
        return data

    def read_int(self, where, size=None, force=False):
        """
        Reads int from memory

        :param int where: address to read from
        :param size: number of bits to read
        :return: the value read
        :rtype: int or BitVec
        :param force: whether to ignore memory permissions
        """
        if size is None:
            size = self.address_bit_size
        assert size in SANE_SIZES
        self._publish("will_read_memory", where, size)

        data = self._memory.read(where, size // 8, force)
        assert (8 * len(data)) == size
        value = Operators.CONCAT(size, *map(Operators.ORD, reversed(data)))

        self._publish("did_read_memory", where, value, size)
        return value

    def write_bytes(self, where: int, data, force: bool = False) -> None:
        """
        Write a concrete or symbolic (or mixed) buffer to memory

        :param where: address to write to
        :param data: data to write
        :param force: whether to ignore memory permissions
        """

        mp = self.memory.map_containing(where)
        # TODO (ehennenfent) - fast write can have some yet-unstudied unintended side effects.
        # At the very least, using it in non-concrete mode will break the symbolic strcmp/strlen models. The 1024 byte
        # minimum is intended to minimize the potential effects of this by ensuring that if there _are_ any other
        # issues, they'll only crop up when we're doing very large writes, which are fairly uncommon.
        if (
            isinstance(mp, AnonMap)
            and isinstance(data, (str, bytes))
            and (mp.end - mp.start + 1) >= len(data) >= 1024
            and not issymbolic(data)
            and self._concrete
        ):
            logger.debug("Using fast write")
            offset = mp._get_offset(where)
            if isinstance(data, str):
                data = bytes(data.encode("utf-8"))
            self._publish("will_write_memory", where, data, 8 * len(data))
            mp._data[offset : offset + len(data)] = data
            self._publish("did_write_memory", where, data, 8 * len(data))
        else:
            for i in range(len(data)):
                self.write_int(where + i, Operators.ORD(data[i]), 8, force)

    def read_bytes(self, where: int, size: int, force: bool = False):
        """
        Read from memory.

        :param where: address to read data from
        :param size: number of bytes
        :param force: whether to ignore memory permissions
        :return: data
        :rtype: list[int or Expression]
        """
        result = []
        for i in range(size):
            result.append(Operators.CHR(self.read_int(where + i, 8, force)))
        return result

    def write_string(
        self, where: int, string: str, max_length: Optional[int] = None, force: bool = False
    ) -> None:
        """
        Writes a string to memory, appending a NULL-terminator at the end.

        :param where: Address to write the string to
        :param string: The string to write to memory
        :param max_length:

        The size in bytes to cap the string at, or None [default] for no
        limit. This includes the NULL terminator.

        :param force: whether to ignore memory permissions
        """

        if max_length is not None:
            string = string[: max_length - 1]

        self.write_bytes(where, string + "\x00", force)

    def read_string(self, where: int, max_length: Optional[int] = None, force: bool = False) -> str:
        """
        Read a NUL-terminated concrete buffer from memory. Stops reading at first symbolic byte.

        :param where: Address to read string from
        :param max_length:
            The size in bytes to cap the string at, or None [default] for no
            limit.
        :param force: whether to ignore memory permissions
        :return: string read
        """
        s = io.BytesIO()
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
        return s.getvalue().decode()

    def push_bytes(self, data, force: bool = False):
        """
        Write `data` to the stack and decrement the stack pointer accordingly.

        :param data: Data to write
        :param force: whether to ignore memory permissions
        """
        self.STACK -= len(data)
        self.write_bytes(self.STACK, data, force)
        return self.STACK

    def pop_bytes(self, nbytes: int, force: bool = False):
        """
        Read `nbytes` from the stack, increment the stack pointer, and return
        data.

        :param nbytes: How many bytes to read
        :param force: whether to ignore memory permissions
        :return: Data read from the stack
        """
        data = self.read_bytes(self.STACK, nbytes, force=force)
        self.STACK += nbytes
        return data

    def push_int(self, value: int, force: bool = False):
        """
        Decrement the stack pointer and write `value` to the stack.

        :param value: The value to write
        :param force: whether to ignore memory permissions
        :return: New stack pointer
        """
        self.STACK -= self.address_bit_size // 8
        self.write_int(self.STACK, value, force=force)
        return self.STACK

    def pop_int(self, force: bool = False):
        """
        Read a value from the stack and increment the stack pointer.

        :param force: whether to ignore memory permissions
        :return: Value read
        """
        value = self.read_int(self.STACK, force=force)
        self.STACK += self.address_bit_size // 8
        return value

    #######################################
    # Decoder
    def _wrap_operands(self, operands):
        """
        Private method to decorate an Operand to our needs based on the
        underlying architecture.
        See :class:`~manticore.core.cpu.abstractcpu.Operand` class
        """
        raise NotImplementedError

    def decode_instruction(self, pc: int):
        """
        This will decode an instruction from memory pointed by `pc`

        :param pc: address of the instruction
        """
        # No dynamic code!!! #TODO!
        # Check if instruction was already decoded
        if pc in self._instruction_cache:
            return self._instruction_cache[pc]

        text = b""

        # Read Instruction from memory
        exec_size = self.memory.max_exec_size(pc, self.max_instr_width)
        instr_memory = self.memory[pc : pc + exec_size]
        for i in range(exec_size):
            # This reads a byte from memory ignoring permissions
            # and concretize it if symbolic

            c = instr_memory[i]
            if issymbolic(c):
                # In case of fully symbolic memory, eagerly get a valid ptr
                if isinstance(self.memory, LazySMemory):
                    try:
                        vals = visitors.simplify_array_select(c)
                        c = bytes([vals[0]])
                    except visitors.ArraySelectSimplifier.ExpressionNotSimple:
                        self._publish("will_solve", self.memory.constraints, c, "get_value")
                        solved = SelectedSolver.instance().get_value(self.memory.constraints, c)
                        self._publish("did_solve", self.memory.constraints, c, "get_value", solved)
                        c = struct.pack("B", solved)
                elif isinstance(c, Constant):
                    c = bytes([c.value])
                else:
                    logger.error("Concretize executable memory %r %r", c, text)
                    raise ConcretizeMemory(
                        self.memory, address=pc, size=8 * self.max_instr_width, policy="INSTRUCTION"
                    )
            text += c

        # Pad potentially incomplete instruction with zeroes
        code = text.ljust(self.max_instr_width, b"\x00")

        try:
            # decode the instruction from code
            insn = self.disasm.disassemble_instruction(code, pc)
        except StopIteration as e:
            raise DecodeException(pc, code)

        # Check that the decoded instruction is contained in executable memory
        if insn.size > exec_size:
            logger.info("Trying to execute instructions from non-executable memory")
            raise InvalidMemoryAccess(pc, "x")

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
        """
        Get the semantic name of an instruction.
        """
        raise NotImplementedError

    def execute(self):
        """
        Decode, and execute one instruction pointed by register PC
        """
        curpc = self.PC
        if self._delayed_event:
            self._icount += 1
            self._publish(
                "did_execute_instruction",
                self._last_pc,
                curpc,
                self.decode_instruction(self._last_pc),
            )
            self._delayed_event = False

        if issymbolic(curpc):
            raise ConcretizeRegister(self, "PC", policy="ALL")
        if not self.memory.access_ok(curpc, "x"):
            raise InvalidMemoryAccess(curpc, "x")

        self._publish("will_decode_instruction", curpc)

        insn = self.decode_instruction(curpc)
        self._last_pc = self.PC

        self._publish("will_execute_instruction", self._last_pc, insn)

        # FIXME (theo) why just return here?
        # hook changed PC, so we trust that there is nothing more to do
        if insn.address != self.PC:
            return

        name = self.canonicalize_instruction_name(insn)

        if logger.level == logging.DEBUG:
            logger.debug(self.render_instruction(insn))
            for l in self.render_registers():
                register_logger.debug(l)

        try:
            if self._concrete and "SYSCALL" in name:
                self.emu.sync_unicorn_to_manticore()
            if self._concrete and "SYSCALL" not in name:
                self.emulate(insn)
                if self.PC == self._break_unicorn_at:
                    logger.debug("Switching from Unicorn to Manticore")
                    self._break_unicorn_at = None
                    self._concrete = False
            else:
                implementation = getattr(self, name, None)

                if implementation is not None:
                    implementation(*insn.operands)

                else:
                    text_bytes = " ".join("%02x" % x for x in insn.bytes)
                    logger.warning(
                        "Unimplemented instruction: 0x%016x:\t%s\t%s\t%s",
                        insn.address,
                        text_bytes,
                        insn.mnemonic,
                        insn.op_str,
                    )
                    self.backup_emulate(insn)
        except (Interruption, Syscall) as e:
            self._delayed_event = True
            raise e
        else:
            self._publish_instruction_as_executed(insn)

    # FIXME(yan): In the case the instruction implementation invokes a system call, we would not be able to
    # publish the did_execute_instruction event from here, so we capture and attach it to the syscall
    # exception for the platform to emit it for us once the syscall has successfully been executed.
    def _publish_instruction_as_executed(self, insn):
        """
        Notify listeners that an instruction has been executed.
        """
        self._icount += 1
        self._publish("did_execute_instruction", self._last_pc, self.PC, insn)

    def emulate(self, insn):
        """
        Pick the right emulate function (maintains API compatiblity)

        :param insn: single instruction to emulate/start emulation from
        """

        if self._concrete:
            self.concrete_emulate(insn)
        else:
            self.backup_emulate(insn)

    def concrete_emulate(self, insn):
        """
        Start executing in Unicorn from this point until we hit a syscall or reach break_unicorn_at

        :param capstone.CsInsn insn: The instruction object to emulate
        """

        if not self.emu:
            self.emu = ConcreteUnicornEmulator(self)
            self.emu._stop_at = self._break_unicorn_at
        try:
            self.emu.emulate(insn)
        except unicorn.UcError as e:
            if e.errno == unicorn.UC_ERR_INSN_INVALID:
                text_bytes = " ".join("%02x" % x for x in insn.bytes)
                logger.error(
                    "Unimplemented instruction: 0x%016x:\t%s\t%s\t%s",
                    insn.address,
                    text_bytes,
                    insn.mnemonic,
                    insn.op_str,
                )
            raise InstructionEmulationError(str(e))

    def backup_emulate(self, insn):
        """
        If we could not handle emulating an instruction, use Unicorn to emulate
        it.

        :param capstone.CsInsn instruction: The instruction object to emulate
        """

        if not hasattr(self, "backup_emu"):
            self.backup_emu = UnicornEmulator(self)
        try:
            self.backup_emu.emulate(insn)
        except unicorn.UcError as e:
            if e.errno == unicorn.UC_ERR_INSN_INVALID:
                text_bytes = " ".join("%02x" % x for x in insn.bytes)
                logger.error(
                    "Unimplemented instruction: 0x%016x:\t%s\t%s\t%s",
                    insn.address,
                    text_bytes,
                    insn.mnemonic,
                    insn.op_str,
                )
            raise InstructionEmulationError(str(e))
        finally:
            # We have been seeing occasional Unicorn issues with it not clearing
            # the backing unicorn instance. Saw fewer issues with the following
            # line present.
            del self.backup_emu

    def render_instruction(self, insn=None):
        try:
            insn = self.instruction
            return f"INSTRUCTION: 0x{insn.address:016x}:\t{insn.mnemonic}\t{insn.op_str}"
        except Exception as e:
            return "{can't decode instruction}"

    def render_register(self, reg_name):
        result = ""

        value = self.read_register(reg_name)

        if issymbolic(value):
            value = str(value)  # coerce the value into a string
            aux = f"{reg_name:3s}: {value:16s}"
            result += aux
        elif isinstance(value, int):
            result += f"{reg_name:3s}: 0x{value:016x}"
        else:
            result += f"{reg_name:3s}: {value!r}"
        return result

    def render_registers(self):
        # FIXME add a context manager at utils that look for all Signal
        # backup, null, use, then restore the list.
        # will disabled_signals(self):
        #    return map(self.render_register, self._regfile.canonical_registers)
        return map(self.render_register, sorted(self._regfile.canonical_registers))

    # Generic string representation
    def __str__(self):
        """
        Returns a string representation of cpu state

        :rtype: str
        :return: name and current value for all the registers.
        """
        result = f"{self.render_instruction()}\n"
        result += "\n".join(self.render_registers())
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
