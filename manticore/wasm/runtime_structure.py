from __future__ import annotations
import typing
import types
import copy
from dataclasses import dataclass
from .executor import Executor
from collections import deque
from wasm.immtypes import BlockImm, BranchImm, BranchTableImm, CallImm, CallIndirectImm
from .types import (
    U32,
    I32,
    Value,
    ValType,
    FunctionType,
    TableType,
    MemoryType,
    GlobalType,
    Byte,
    Name,
    ExternType,
    FuncIdx,
    TableIdx,
    MemIdx,
    GlobalIdx,
    WASMExpression,
    Instruction,
)
from ..core.smtlib import BitVec


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


Result: type = typing.Union[typing.Sequence[Value]]  # Could also be an exception (trap)
Addr: type = type("Addr", (int,), {})
FuncAddr: type = type("FuncAddr", (Addr,), {})
TableAddr: type = type("TableAddr", (Addr,), {})
MemAddr: type = type("MemAddr", (Addr,), {})
GlobalAddr: type = type("GlobalAddr", (Addr,), {})

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
    funcs: typing.List[ProtoFuncInst]
    tables: typing.List[TableInst]
    mems: typing.List[MemInst]
    globals: typing.List[GlobalInst]

    def __init__(self):
        self.funcs = []
        self.tables = []
        self.mems = []
        self.globals = []

    def __getstate__(self):
        state = {
            "funcs": self.funcs,
            "tables": self.tables,
            "mems": self.mems,
            "globals": self.globals,
        }
        return state

    def __setstate__(self, state):
        self.funcs = state["funcs"]
        self.tables = state["tables"]
        self.mems = state["mems"]
        self.globals = state["globals"]


class ModuleInstance:
    __slots__ = [
        "types",
        "funcaddrs",
        "tableaddrs",
        "memaddrs",
        "globaladdrs",
        "exports",
        "executor",
        "_instruction_queue",
    ]

    types: typing.List[FunctionType]
    funcaddrs: typing.List[FuncAddr]
    tableaddrs: typing.List[TableAddr]
    memaddrs: typing.List[MemAddr]
    globaladdrs: typing.List[GlobalAddr]
    exports: typing.List[ExportInst]
    executor: Executor
    _instruction_queue: typing.Deque[Instruction]

    def __init__(self):
        self.types = []
        self.funcaddrs = []
        self.tableaddrs = []
        self.memaddrs = []
        self.globaladdrs = []
        self.exports = []
        self.executor = Executor()
        self._instruction_queue = deque()

    def __getstate__(self):
        state = {
            "types": self.types,
            "funcaddrs": self.funcaddrs,
            "tableaddrs": self.tableaddrs,
            "memaddrs": self.memaddrs,
            "globaladdrs": self.globaladdrs,
            "exports": self.exports,
            "executor": self.executor,
            "_instruction_queue": self._instruction_queue,
        }
        return state

    def __setstate__(self, state):
        self.types = state["types"]
        self.funcaddrs = state["funcaddrs"]
        self.tableaddrs = state["tableaddrs"]
        self.memaddrs = state["memaddrs"]
        self.globaladdrs = state["globaladdrs"]
        self.exports = state["exports"]
        self.executor = state["executor"]
        self._instruction_queue = state["_instruction_queue"]

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

        vals = [self.exec_expression(store, stack, gb.init) for gb in module.globals]

        last_frame = stack.pop()
        assert isinstance(last_frame, Activation)
        assert last_frame.frame == aux_frame

        # #6, #7, #8
        self.allocate(store, module, extern_vals, vals)
        f = Frame(locals=[], module=self)
        stack.push(Activation(0, f))

        # #9 & #13
        for elem in module.elem:
            eoval = self.exec_expression(store, stack, elem.offset)
            assert isinstance(eoval, I32)
            assert elem.table in range(len(self.tableaddrs))
            tableaddr: TableAddr = self.tableaddrs[elem.table]
            assert tableaddr in range(len(store.tables))
            tableinst: TableInst = store.tables[tableaddr]
            eend = eoval + len(elem.init)
            assert eend <= len(tableinst.elem)

            FuncIdx: FuncIdx
            for j, FuncIdx in enumerate(elem.init):
                assert FuncIdx in range(len(self.funcaddrs))
                funcaddr = self.funcaddrs[FuncIdx]
                tableinst.elem[eoval + j] = funcaddr

        # #10 & #14
        for data in module.data:
            doval = self.exec_expression(store, stack, data.offset)
            assert isinstance(doval, I32), f"{type(doval)} is not an I32"
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

        print("Initialization Complete")

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
            if isinstance(export_i.desc, FuncIdx):
                val = self.funcaddrs[export_i.desc]
            if isinstance(export_i.desc, TableIdx):
                val = self.tableaddrs[export_i.desc]
            if isinstance(export_i.desc, MemIdx):
                val = self.memaddrs[export_i.desc]
            if isinstance(export_i.desc, GlobalIdx):
                val = self.globaladdrs[export_i.desc]
            self.exports.append(ExportInst(export_i.name, val))

    def invoke_by_name(self, name: str, stack, store, argv):
        for export in self.exports:
            if export.name == name and isinstance(export.value, FuncAddr):
                return self.invoke(stack, export.value, store, argv)

    def invoke(
        self, stack: "Stack", funcaddr: FuncAddr, store: Store, argv: typing.List[Value]
    ) -> typing.List[Value]:
        assert funcaddr in range(len(store.funcs))
        funcinst = store.funcs[funcaddr]
        ty = funcinst.type
        assert len(ty.param_types) == len(argv)
        # for t, v in zip(ty.param_types, argv):
        #     assert type(v) == type(t)

        dummy_frame = Frame([], ModuleInstance())
        stack.push(dummy_frame)
        for v in argv:
            stack.push(v)

        # https://www.w3.org/TR/wasm-core-1/#exec-invoke
        self._invoke_inner(stack, funcaddr, store)

        return [stack.pop() for _i in range(len(ty.result_types))]

    def _invoke_inner(self, stack: "Stack", funcaddr: FuncAddr, store: Store):
        assert funcaddr in range(len(store.funcs))
        f: ProtoFuncInst = store.funcs[funcaddr]
        ty = f.type
        assert len(ty.result_types) <= 1
        locals = [stack.pop() for _t in ty.param_types]
        if isinstance(f, HostFunc):
            res = list(f.hostcode(*locals))
            print("HostFunc returned", res)
            assert len(res) == len(ty.result_types)
            for r, t in zip(res, ty.result_types):
                stack.push(t.cast(r))
        else:
            for cast in f.code.locals:
                locals.append(cast(0))
            frame = Frame(locals, f.module)
            stack.push(Activation(len(ty.result_types), frame))
            self.block(store, stack, ty.result_types, f.code.body)

    def exec_expression(self, store: Store, stack: "Stack", expr: WASMExpression):
        self.push_instructions(expr)
        while self.exec_instruction(store, stack):
            pass
        return stack.pop()

    def enter_instruction(self, insts, label: "Label", stack: "Stack"):
        stack.push(label)
        self.push_instructions(insts)

    def exit_instruction(self, stack: "Stack"):
        label_idx = stack.find_type(Label)
        if label_idx is not None:
            i = -1
            while isinstance(stack.data[i], Value.__args__):
                i -= 1
            vals = [stack.pop() for _i in range(abs(i))]  # TODO  - Confirm this isn't an off-by-one
            label = stack.pop()
            assert isinstance(label, Label)
            for v in vals[::-1]:
                stack.push(v)

            self.push_instructions(label.instr)

    def push_instructions(self, insts: WASMExpression):
        for i in insts[::-1]:
            self._instruction_queue.append(i)

    def exec_instruction(self, store, stack) -> bool:
        if self._instruction_queue:
            inst = self._instruction_queue.pop()
            print(f"{inst.opcode}:", inst.mnemonic, f"({debug(inst.imm)})" if inst.imm else "")
            if 0x2 <= inst.opcode <= 0x11:
                if inst.opcode == 0x02:
                    self.block(store, stack, [], [])  # TODO
                elif inst.opcode == 0x03:
                    self.loop(store, stack, inst.imm)
                elif inst.opcode == 0x04:
                    self.if_(store, stack, inst.imm)
                elif inst.opcode == 0x05:
                    self.else_(store, stack)
                elif inst.opcode == 0x0B:
                    self.end(store, stack)
                elif inst.opcode == 0x0C:
                    self.br(store, stack, inst.imm)
                elif inst.opcode == 0x0D:
                    self.br_if(store, stack, inst.imm)
                elif inst.opcode == 0x0E:
                    self.br_table(store, stack, inst.imm)
                elif inst.opcode == 0x0F:
                    self.return_(store, stack)
                elif inst.opcode == 0x10:
                    self.call(store, stack, inst.imm)
                elif inst.opcode == 0x11:
                    self.call_indirect(store, stack, inst.imm)
                else:
                    raise Exception("Unhandled control flow instruction")
            else:
                self.executor.dispatch(inst, store, stack)
            return True
        elif stack.find_type(Label):
            self.exit_instruction(stack)
            return True
        return False

    def block(
        self, store: "Store", stack: "Stack", ret_type: typing.List[ValType], insts: WASMExpression
    ):
        arity = len(ret_type)
        l = Label(arity, list(self._instruction_queue.copy()))
        self._instruction_queue.clear()
        self.enter_instruction(insts, l, stack)

    def loop(self, store: "Store", stack: "Stack", imm: BlockImm):
        raise NotImplementedError("loop")

    def if_(self, store: "Store", stack: "Stack", imm: BlockImm):
        raise NotImplementedError("if")

    def else_(self, store: "Store", stack: "Stack"):
        raise NotImplementedError("else")

    def end(self, store: "Store", stack: "Stack"):
        pass

    def br(self, store: "Store", stack: "Stack", imm: BranchImm):
        raise NotImplementedError("br")

    def br_if(self, store: "Store", stack: "Stack", imm: BranchImm):
        raise NotImplementedError("br_if")

    def br_table(self, store: "Store", stack: "Stack", imm: BranchTableImm):
        raise NotImplementedError("br_table")

    def return_(self, store: "Store", stack: "Stack"):
        raise NotImplementedError("return")

    def call(self, store: "Store", stack: "Stack", imm: CallImm):
        f = stack.get_frame()
        assert imm.function_index in range(len(f.module.funcaddrs))
        a = f.module.funcaddrs[imm.function_index]
        self._invoke_inner(stack, a, store)

    def call_indirect(self, store: "Store", stack: "Stack", imm: CallIndirectImm):
        raise NotImplementedError("call_indirect")


@dataclass
class Label:
    arity: int
    instr: typing.List[Instruction]


@dataclass
class Frame:
    locals: typing.List[Value]
    module: ModuleInstance


@dataclass
class Activation:
    arity: int
    frame: Frame


class Stack:
    data: typing.Deque[typing.Union[Value, Label, Activation]]

    def __init__(self, init_data=None):
        self.data = init_data if init_data else deque()

    def __getstate__(self):
        state = {"data": self.data}
        return state

    def __setstate__(self, state):
        self.data = state["data"]

    def push(self, val: typing.Union[Value, Label, Activation]) -> None:
        # print("Pushing", val)
        self.data.append(val)

    def pop(self) -> typing.Union[Value, Label, Activation]:
        # print("Removing", self.peek())
        return self.data.pop()

    def peek(self):
        return self.data[-1]

    def empty(self):
        return len(self.data) == 0

    def has_type_on_top(self, t: type, n: int):
        for i in range(1, n + 1):
            assert isinstance(self.data[i * -1], (t, BitVec)), f"{type(self.data[i * -1])} is not an {t}!"
        return True

    def find_type(self, t: type):
        for idx, v in enumerate(reversed(self.data)):
            if isinstance(v, t):
                return -1 * idx
        return None

    def pop_all(self):
        out = copy.copy(self.data)
        self.data.clear()
        return out

    def get_frame(self) -> Frame:
        for item in reversed(self.data):
            if isinstance(item, Activation):
                return item.frame
            if isinstance(item, Frame):
                return item


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
