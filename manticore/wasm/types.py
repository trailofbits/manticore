import typing
from dataclasses import dataclass

# TODO - These need to be symbolic fixed-size representations
U32 = int
U64 = int
I32 = int
I64 = int
F32 = float
F64 = float
Byte = int

ValType = typing.Union[U32, U64, F32, F64]
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


MemoryType = LimitType
ExternType = typing.Union[FunctionType, TableType, MemoryType, GlobalType]
