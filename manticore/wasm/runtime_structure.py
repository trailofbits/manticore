import typing
import types
from dataclasses import dataclass
from wasm.decode import Instruction
from .types import (
    U32,
    I32,
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
        """
        https://www.w3.org/TR/wasm-core-1/#instantiation%E2%91%A1
        :param store:
        :param module:
        :param extern_vals:
        :return:
        """
        # #1 Assert: module is valid
        assert module  # close enough

        # TODO: #2 Assert: module is valid with external types _externtype_ classifying its imports.
        # for ext in module.imports:
        #     assert isinstance(ext, ExternType.__args__)

        # #3 Assert the same number of imports and external values
        assert len(module.imports) == len(extern_vals)

        # #4 TODO

        # #5
        stack = Stack()

        aux_mod = ModuleInstance()
        aux_mod.globaladdrs = [i for i in extern_vals if isinstance(i, GlobalAddr)]
        aux_frame = Frame([], aux_mod)
        stack.push(Activation(0, aux_frame))

        vals = []  # TODO: implement exec_global [exec_global(gb) for gb in module.globals]

        last_frame = stack.pop()
        assert isinstance(last_frame, Activation)
        assert last_frame.frame == aux_frame

        # #6, #7, #8
        self.allocate(store, module, extern_vals, vals)
        f = Frame(locals=[], module=self)
        stack.push(Activation(0, f))

        # #9 & #13
        for elem in module.elem:
            eoval = I32(0)  # exec_elem(elem.offset) TODO - implement exec_element
            assert isinstance(eoval, I32)
            assert elem.table in range(len(self.tableaddrs))
            tableaddr: TableAddr = self.tableaddrs[elem.table]
            assert tableaddr in range(len(store.tables))
            tableinst: TableInst = store.tables[tableaddr]
            eend = eoval + len(elem.init)
            assert eend <= len(tableinst.elem)

            funcidx: Indices.funcidx
            for j, funcidx in enumerate(elem.init):
                assert funcidx in range(len(self.funcaddrs))
                funcaddr = self.funcaddrs[funcidx]
                tableinst.elem[eoval + j] = funcaddr

        # #10 & #14
        for data in module.data:
            doval = I32(0)  # exec_data(data.offset) TODO - implement exec_data
            assert isinstance(doval, I32)
            assert data.data in range(len(self.memaddrs))
            memaddr = self.memaddrs[data.data]
            assert memaddr in range(len(store.mems))
            meminst = store.mems[memaddr]
            dend = doval + len(data.init)
            assert dend <= len(meminst.data)

            for j, b in enumerate(data.init):
                meminst.data[doval + j] = b

        # #11 & #12
        last_frame = stack.pop()
        assert isinstance(last_frame, Activation)
        assert last_frame.frame == f

        # #15  TODO run start function

    def allocate(
        self,
        store: Store,
        module: "Module",
        extern_vals: typing.List[ExternVal],
        values: typing.List[Value],
    ):
        """
        https://www.w3.org/TR/wasm-core-1/#allocation%E2%91%A0
        :param store:
        :param module:
        :param extern_vals:
        :param values:
        :return:
        """
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


class Stack:
    data: typing.List[typing.Union[Value, Label, Activation]]

    def __init__(self, init_data=None):
        self.data = init_data if init_data else []

    def push(self, val: typing.Union[Value, Label, Activation]) -> None:
        self.data.append(val)

    def pop(self) -> typing.Union[Value, Label, Activation]:
        return self.data.pop()


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
