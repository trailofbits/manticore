import typing
from dataclasses import dataclass
from ..core.smtlib import issymbolic, BitVec
from ctypes import *
import wasm
import struct
from ..core.state import Concretize

# Do I like this? No. Is it necessary to get mypy to pass without destroying the WASM type system? Yes.
# Look how much cleaner the version below is instead of having a separate class for every type...
"""
U32: type = type("U32", (int,), {})
U64: type = type("U64", (int,), {})
"""


class U32(int):
    pass


class U64(int):
    pass


def debug(imm):
    """
    Attempts to pull meaningful data out of an immediate, which has a dynamic GeneratedStructure type

    :param imm: the instruction immediate
    :return: a printable representation of the immediate, or the immediate itself
    """
    if hasattr(imm, "value"):
        return imm.value
    if hasattr(imm, "function_index"):
        return f"Func Idx {imm.function_index}"
    if hasattr(imm, "offset"):
        return f"Offset {imm.offset}"
    if hasattr(imm, "local_index"):
        return f"Local {imm.local_index}"
    if hasattr(imm, "global_index"):
        return f"Global {imm.global_index}"
    return getattr(imm, "value", imm)


def _reinterpret(ty1: type, ty2: type, val):
    """
    Attempts to convert a value from one ctypes type to another

    :param ty1: The type of the value
    :param ty2: The desired type of the value
    :param val: The value itself
    :return: The converted value
    """
    ptr = pointer(ty1(val))
    # mypy worries that `contents` won't always exist for the pointer type
    return cast(ptr, POINTER(ty2)).contents.value  # type: ignore


class I32(int):
    """
    Subclass of int that's restricted to 32-bit values
    """

    def __new__(cls, val):
        val = struct.unpack("i", c_int32(int(val)))[0]
        return super(I32, cls).__new__(cls, val)

    @classmethod
    def cast(cls, other):
        """
        :param other: Value to convert to I32
        :return: If other is symbolic, other. Otherwise, I32(other)
        """
        if issymbolic(other):
            return other
        return cls(other)

    @staticmethod
    def to_unsigned(val):
        """
        Reinterprets the argument from a signed integer to an unsigned 32-bit integer

        :param val: Signed integer to reinterpret
        :return: The unsigned equivalent
        """
        return _reinterpret(c_int32, c_uint32, val)


class I64(int):
    """
    Subclass of int that's restricted to 64-bit values
    """

    def __new__(cls, val):
        val = struct.unpack("q", c_int64(int(val)))[0]
        return super(I64, cls).__new__(cls, val)

    @classmethod
    def cast(cls, other):
        """
        :param other: Value to convert to I64
        :return: If other is symbolic, other. Otherwise, I64(other)
        """
        if issymbolic(other):
            return other
        return cls(other)

    @staticmethod
    def to_unsigned(val):
        """
        Reinterprets the argument from a signed integer to an unsigned 64-bit integer

        :param val: Signed integer to reinterpret
        :return: The unsigned equivalent
        """
        return _reinterpret(c_int64, c_uint64, val)


class F32(float):
    """
    Subclass of float that's restricted to 32-bit values
    """

    def __new__(cls, val):
        if isinstance(val, int):
            val = _reinterpret(c_int32, c_float, val & 0xFFFFFFFF)
        val = struct.unpack("f", c_float(val))[0]
        self = super(F32, cls).__new__(cls, val)
        self.integer = val
        return self

    @classmethod
    def cast(cls, other):
        """
        :param other: Value to convert to F32
        :return: If other is symbolic, other. Otherwise, F32(other)
        """
        if issymbolic(other):
            return other
        return cls(other)


class F64(float):
    """
    Subclass of float that's restricted to 64-bit values
    """

    def __new__(cls, val):
        if isinstance(val, int):
            val = _reinterpret(c_int64, c_double, val)
        val = struct.unpack("d", c_double(val))[0]
        self = super(F64, cls).__new__(cls, val)
        self.integer = val
        return self

    @classmethod
    def cast(cls, other):
        """
        :param other: Value to convert to F64
        :return: If other is symbolic, other. Otherwise, F64(other)
        """
        if issymbolic(other):
            return other
        return cls(other)


ValType = type  #: https://www.w3.org/TR/wasm-core-1/#syntax-valtype
Value_t = (I32, I64, F32, F64, BitVec)
# Value = typing.TypeVar('Value', I32, I64, F32, F64, BitVec)  #: https://www.w3.org/TR/wasm-core-1/#syntax-val
Value = typing.Union[I32, I64, F32, F64, BitVec]  #: https://www.w3.org/TR/wasm-core-1/#syntax-val


class Name(str):
    pass


@dataclass
class FunctionType:
    """
    https://www.w3.org/TR/wasm-core-1/#syntax-functype
    """

    param_types: typing.List[ValType]  #: Sequential types of each of the parameters
    result_types: typing.List[ValType]  #: Sequential types of each of the return values


@dataclass
class LimitType:
    """
    https://www.w3.org/TR/wasm-core-1/#syntax-limits
    """

    min: U32
    max: typing.Optional[U32]


@dataclass
class TableType:
    """https://www.w3.org/TR/wasm-core-1/#syntax-tabletype"""

    limits: LimitType  #: Minimum and maximum size of the table
    elemtype: type  #: the type ot the element. Currently, the only element type is `funcref`


@dataclass
class GlobalType:
    """https://www.w3.org/TR/wasm-core-1/#syntax-globaltype"""

    mut: bool  #: Whether or not this global is mutable
    value: ValType  #: The value of the global


# https://www.w3.org/TR/wasm-core-1/#indices%E2%91%A0
class TypeIdx(U32):
    pass


class FuncIdx(U32):
    pass


class TableIdx(U32):
    pass


class MemIdx(U32):
    pass


class GlobalIdx(U32):
    pass


class LocalIdx(U32):
    pass


class LabelIdx(U32):
    pass


@dataclass
class BlockImm:
    sig: int


@dataclass
class BranchImm:
    relative_depth: U32


@dataclass
class BranchTableImm:
    target_count: U32
    target_table: typing.List[U32]
    default_target: U32


@dataclass
class CallImm:
    function_index: U32


@dataclass
class CallIndirectImm:
    type_index: U32
    reserved: U32


@dataclass
class LocalVarXsImm:
    local_index: U32


@dataclass
class GlobalVarXsImm:
    global_index: U32


@dataclass
class MemoryImm:
    flags: U32
    offset: U32


@dataclass
class CurGrowMemImm:
    reserved: bool


@dataclass
class I32ConstImm:
    value: I32


@dataclass
class I64ConstImm:
    value: I64


@dataclass
class F32ConstImm:
    value: F32


@dataclass
class F64ConstImm:
    value: F64


ImmType = typing.Union[
    BlockImm,
    BranchImm,
    BranchTableImm,
    CallImm,
    CallIndirectImm,
    LocalVarXsImm,
    GlobalVarXsImm,
    MemoryImm,
    CurGrowMemImm,
    I32ConstImm,
    F32ConstImm,
    F64ConstImm,
]  #: Types of all immediates


class Instruction:
    """Internal instruction class that's pickle-friendly and works with the type system """

    __slots__ = ["opcode", "mnemonic", "imm"]
    opcode: int  #: Opcode, used for dispatching instructions
    mnemonic: str  #: Used for debugging
    imm: ImmType  #: A class with the immediate data for this instruction

    def __init__(self, inst: wasm.decode.Instruction, imm=None):
        self.opcode = inst.op.id
        self.mnemonic = inst.op.mnemonic
        self.imm = imm

    def __repr__(self):
        return f"<Instruction: {self.mnemonic} ({debug(self.imm)})>"


MemoryType = LimitType  #: https://www.w3.org/TR/wasm-core-1/#syntax-memtype
ExternType = typing.Union[
    FunctionType, TableType, MemoryType, GlobalType
]  #: https://www.w3.org/TR/wasm-core-1/#external-types%E2%91%A0
WASMExpression = typing.List[Instruction]


def convert_instructions(inst_seq) -> WASMExpression:
    """
    Converts instructions output from the parser into full-fledged Python objects that will work with Manticore.
    This is necessary because the pywasm module uses lots of reflection to generate structures on the fly, which
    doesn't play nicely with Pickle or the type system. That's why we need the `debug` method above to print out
    immediates, and also why we've created a separate class for every different type of immediate.

    :param inst_seq: Sequence of raw instructions to process
    :return: The properly-typed instruction sequence in a format Manticore can use
    """
    out = []
    if not isinstance(inst_seq, list):
        inst_seq = list(wasm.decode_bytecode(inst_seq))
    i: wasm.decode.Instruction
    for i in inst_seq:
        if 0x02 <= i.op.id <= 0x04:
            out.append(Instruction(i, BlockImm(i.imm.sig)))
        elif i.op.id in (0x0C, 0x0D):
            out.append(Instruction(i, BranchImm(i.imm.relative_depth)))
        elif i.op.id == 0x0E:
            out.append(
                Instruction(
                    i, BranchTableImm(i.imm.target_count, i.imm.target_table, i.imm.default_target)
                )
            )
        elif i.op.id == 0x10:
            out.append(Instruction(i, CallImm(i.imm.function_index)))
        elif i.op.id == 0x11:
            out.append(Instruction(i, CallIndirectImm(i.imm.type_index, i.imm.reserved)))
        elif 0x20 <= i.op.id <= 0x22:
            out.append(Instruction(i, LocalVarXsImm(i.imm.local_index)))
        elif i.op.id in (0x23, 0x24):
            out.append(Instruction(i, GlobalVarXsImm(i.imm.global_index)))
        elif 0x28 <= i.op.id <= 0x3E:
            out.append(Instruction(i, MemoryImm(i.imm.flags, i.imm.offset)))
        elif i.op.id in (0x3F, 0x40):
            out.append(Instruction(i, CurGrowMemImm(i.imm.reserved)))
        elif i.op.id == 0x41:
            out.append(Instruction(i, I32ConstImm(i.imm.value)))
        elif i.op.id == 0x42:
            out.append(Instruction(i, I64ConstImm(i.imm.value)))
        elif i.op.id == 0x43:
            out.append(Instruction(i, F32ConstImm(i.imm.value)))
        elif i.op.id == 0x44:
            out.append(Instruction(i, F64ConstImm(i.imm.value)))
        else:
            out.append(Instruction(i))

    return out


class Trap(Exception):
    """
    Subclass of Exception, used for WASM errors
    """

    pass


class UnreachableInstructionTrap(Trap):
    def __init__(self):
        super().__init__("Tried to execute an unreachable instruction")


class ZeroDivisionTrap(Trap):
    def __init__(self):
        super().__init__("Zero division")


class OverflowDivisionTrap(Trap):
    def __init__(self):
        super().__init__("Overflow in signed division")


class NonExistentFunctionCallTrap(Trap):
    def __init__(self):
        super().__init__("Indirect call to non-existent function")


class OutOfBoundsMemoryTrap(Trap):
    def __init__(self, addr):
        super().__init__("Out of bounds memory access at " + hex(addr))


class InvalidConversionTrap(Trap):
    def __init__(self, ty, val):
        super().__init__("Can't convert " + str(val) + " to " + str(ty))


class TypeMismatchTrap(Trap):
    def __init__(self, ty1, ty2):
        super().__init__(f"Type signature mismatch: {ty1} != {ty2}")


class ConcretizeStack(Concretize):
    """Tells Manticore to concretize the value `depth` values from the end of the stack. """

    def __init__(self, depth: int, ty: type, message: str, expression, policy=None, **kwargs):
        """
        :param depth: Index in the stack (should typically be negative)
        :param ty: The type to cast the
        :param message: Debug message describing the reason for concretization
        :param expression: The expression to concretize, either a Value or a BitVec
        """

        def setstate(state, value):
            state.platform.stack.data[depth] = ty(value)

        super().__init__(message, expression, setstate, policy, **kwargs)


class MissingExportException(Trap):
    def __init__(self, name):
        self.name = name
        super().__init__(f"Couldn't find an export called `{name}`")
