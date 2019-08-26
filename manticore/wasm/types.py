import typing
from dataclasses import dataclass
from ..core.smtlib import issymbolic, BitVec
from ctypes import *
import wasm
import struct

U32: type = type("U32", (int,), {})
U64: type = type("U64", (int,), {})
Byte: type = type("Byte", (int,), {})


def debug(imm):
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


class I32(int):
    def __new__(cls, val):
        val &= 0xFFFFFFFF
        if val > 0x7FFFFFFF:
            val = struct.unpack("i", struct.pack("I", val))[
                0
            ]  # TODO - this is probably unsound overall
        return super(I32, cls).__new__(cls, val)

    @classmethod
    def cast(cls, other):
        if issymbolic(other):
            return other
        return I32(other)


class I64(int):
    @classmethod
    def cast(cls, other):
        if issymbolic(other):
            return other
        return I64(other)


class F32(float):
    def __new__(cls, val):
        if int==type(val):
            val &= 0xFFFFFFFF
            ptr = pointer(c_int(val))
            fl = cast(ptr, POINTER(c_float))
            val = fl.contents.value
        self=super(F32, cls).__new__(cls,val)
        self.integer = val
        return self

    @classmethod
    def cast(cls, other):
        if issymbolic(other):
            return other
        return F32(other)


class F64(float):
    def __new__(cls, val):
        if int==type(val):
            ptr = pointer(c_ulong(val))
            fl = cast(ptr, POINTER(c_double))
            val = fl.contents.value
        return super(F64, cls).__new__(cls,val)

    @classmethod
    def cast(cls, other):
        if issymbolic(other):
            return other
        return F64(other)


ValType = typing.Union[type(I32), type(I64), type(F32), type(F64), type(BitVec)]
Value = typing.Union[I32, I64, F32, F64, BitVec]
Name: type = type("Name", (str,), {})
ResultType = typing.Optional[
    ValType
]  # This _should_ be a sequence, but WASM only allows single return values


@dataclass
class FunctionType:
    param_types: typing.List[ValType]
    result_types: typing.List[ValType]


@dataclass
class LimitType:
    min: U32
    max: typing.Optional[U32]


@dataclass
class TableType:
    limits: LimitType
    elemtype: type  # Currently, the only element type is `funcref`


@dataclass
class GlobalType:
    mut: bool
    value: ValType


TypeIdx: type = type("TypeIdx", (U32,), {})
FuncIdx: type = type("FuncIdx", (U32,), {})
TableIdx: type = type("TableIdx", (U32,), {})
MemIdx: type = type("MemIdx", (U32,), {})
GlobalIdx: type = type("GlobalIdx", (U32,), {})
LocalIdx: type = type("LocalIdx", (U32,), {})
LabelIdx: type = type("LabelIdx", (U32,), {})


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


ImmType: type = typing.Union[
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
]


class Instruction:
    __slots__ = ["opcode", "mnemonic", "imm"]
    opcode: int
    mnemonic: str
    imm: ImmType

    def __init__(self, inst: wasm.decode.Instruction, imm=None):
        self.opcode = inst.op.id
        self.mnemonic = inst.op.mnemonic
        self.imm = imm

    def __repr__(self):
        return f"<Instruction: {self.mnemonic} ({debug(self.imm)})>"


MemoryType = LimitType
ExternType = typing.Union[FunctionType, TableType, MemoryType, GlobalType]
WASMExpression = typing.List[Instruction]


def convert_instructions(inst_seq) -> WASMExpression:
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
