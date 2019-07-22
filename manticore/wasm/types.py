import typing
from dataclasses import dataclass

# TODO - These need to be symbolic fixed-size representations
U32: type = type("U32", (int,), {})
U64: type = type("U64", (int,), {})
I32: type = type("I32", (int,), {})
I64: type = type("I64", (int,), {})
F32: type = type("F32", (float,), {})
F64: type = type("F64", (float,), {})
Byte: type = type("Byte", (int,), {})

ValType = typing.Union[U32, U64, F32, F64]
Value = typing.Union[I32, I64, F32, F64]
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


class Indices:
    typeidx: type = type("typeidx", (U32,), {})
    funcidx: type = type("funcidx", (U32,), {})
    tableidx: type = type("tableidx", (U32,), {})
    memidx: type = type("memidx", (U32,), {})
    globalidx: type = type("globalidx", (U32,), {})
    localidx: type = type("localidx", (U32,), {})
    labelidx: type = type("labelidx", (U32,), {})


MemoryType = LimitType
ExternType = typing.Union[FunctionType, TableType, MemoryType, GlobalType]
