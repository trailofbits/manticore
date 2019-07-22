import typing
import types
from dataclasses import dataclass
from wasm.decode import Instruction
from .types import (
    U32,
    Value,
    FunctionType,
    TableType,
    MemoryType,
    GlobalType,
    Byte,
    Name,
    ExternType,
    Indices,
)

Result: type = typing.Union[typing.Sequence[Value]]  # Could also be an exception (trap)
Addr: type = type("Addr", (int,), {})
FuncAddr: type = type("Addr", (Addr,), {})
TableAddr: type = type("Addr", (Addr,), {})
MemAddr: type = type("Addr", (Addr,), {})
GlobalAddr: type = type("Addr", (Addr,), {})

ExternVal: type = typing.Union[FuncAddr, TableAddr, MemAddr, GlobalAddr]
FuncElem: type = typing.Optional[FuncAddr]


@dataclass
class ProtoFuncInst:
    type: FunctionType


@dataclass
class TableInst:
    elem: typing.List[FuncElem]
    max: typing.Optional[U32]


@dataclass
class MemInst:
    data: typing.List[Byte]
    max: typing.Optional[U32]


@dataclass
class GlobalInst:
    value: Value
    mut: bool


@dataclass
class ExportInst:
    name: Name
    value: ExternVal


class Store:
    __slots__ = ["funcs", "tables", "mems", "globals"]
    funcs: typing.Sequence[ProtoFuncInst]
    tables: typing.Sequence[TableInst]
    mems: typing.Sequence[MemInst]
    globals: typing.Sequence[GlobalInst]

    def __init__(self):
        self.funcs = []
        self.tables = []
        self.mems = []
        self.globals = []


class ModuleInstance:
    __slots__ = ["types", "funcaddrs", "tableaddrs", "memaddrs", "globaladdrs", "exports"]
    types: typing.Sequence[FunctionType]
    funcaddrs: typing.Sequence[FuncAddr]
    tableaddrs: typing.Sequence[TableAddr]
    memaddrs: typing.Sequence[MemAddr]
    globaladdrs: typing.Sequence[GlobalAddr]
    exports: typing.Sequence[ExportInst]

    def __init__(self):
        self.types = []
        self.funcaddrs = []
        self.tableaddrs = []
        self.memaddrs = []
        self.globaladdrs = []
        self.exports = []

    def instantiate(self, store: Store, module: "Module", extern_vals: typing.List[ExternVal]):
        # #1 Assert: module is valid
        assert module  # close enough

        # TODO: #2 Assert: module is valid with external types _externtype_ classifying its imports.
        # for ext in module.imports:
        #     assert isinstance(ext, ExternType.__args__)

        # #3 Assert the same number of imports and external values
        assert len(module.imports) == len(extern_vals)

        # #4 TODO

        # #5

        # #6

        # #7
        # f = Frame(locals=[], module=self)

        # #8

        # #9

        # #10

        # #11

        # #12

        # #13

        # #14

        # #15

    def allocate(
        self,
        store: Store,
        module: "Module",
        extern_vals: typing.List[ExternVal],
        values: typing.List[Value],
    ):
        self.types = module.types

        for ev in extern_vals:
            if isinstance(ev, FuncAddr):
                self.funcaddrs.append(ev)
            if isinstance(ev, TableAddr):
                self.tableaddrs.append(ev)
            if isinstance(ev, MemAddr):
                self.memaddrs.append(ev)
            if isinstance(ev, GlobalAddr):
                self.globaladdrs.append(ev)

        for func_i in module.funcs:
            self.funcaddrs.append(func_i.allocate(store, self))
        for table_i in module.tables:
            self.tableaddrs.append(table_i.allocate(store, table_i.type))
        for memory_i in module.mems:
            self.memaddrs.append(memory_i.allocate(store, memory_i.type))
        for idx, global_i in enumerate(module.globals):
            assert isinstance(values[idx], global_i.type)  # TODO - might be wrong
            self.globaladdrs.append(global_i.allocate(store, global_i.type, values[idx]))
        for idx, export_i in enumerate(module.exports):
            if isinstance(export_i.desc, Indices.funcidx):
                val = self.funcaddrs[export_i.desc]
            if isinstance(export_i.desc, Indices.tableidx):
                val = self.tableaddrs[export_i.desc]
            if isinstance(export_i.desc, Indices.memidx):
                val = self.memaddrs[export_i.desc]
            if isinstance(export_i.desc, Indices.globalidx):
                val = self.globaladdrs[export_i.desc]
            self.exports.append(ExportInst(export_i.name, val))


@dataclass
class Label:
    arity: int
    instr: typing.Sequence[Instruction]


@dataclass
class Frame:
    locals: typing.Sequence[Value]
    module: ModuleInstance


@dataclass
class Activation:
    arity: int
    frame: Frame


@dataclass
class Stack:
    data: typing.List[typing.Union[Value, Label, Activation]]


@dataclass
class FuncInst(ProtoFuncInst):
    module: ModuleInstance
    code: "Function"


@dataclass
class HostFunc(ProtoFuncInst):
    hostcode: types.FunctionType

    def allocate(
        self, store: Store, functype: FunctionType, host_func: types.FunctionType
    ) -> FuncAddr:
        pass
