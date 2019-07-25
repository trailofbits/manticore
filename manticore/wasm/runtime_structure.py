import typing
import types
import copy
from dataclasses import dataclass
from wasm.decode import Instruction
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
    Indices,
    WASMExpression,
)


def debug(imm):
    return getattr(imm, "value", imm)


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
    funcs: typing.List[ProtoFuncInst]
    tables: typing.List[TableInst]
    mems: typing.List[MemInst]
    globals: typing.List[GlobalInst]

    def __init__(self):
        self.funcs = []
        self.tables = []
        self.mems = []
        self.globals = []


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
        "_pc",
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

            funcidx: Indices.funcidx
            for j, funcidx in enumerate(elem.init):
                assert funcidx in range(len(self.funcaddrs))
                funcaddr = self.funcaddrs[funcidx]
                tableinst.elem[eoval + j] = funcaddr

        # #10 & #14
        for data in module.data:
            doval = self.exec_expression(store, stack, data.offset)
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
            if isinstance(export_i.desc, Indices.funcidx):
                val = self.funcaddrs[export_i.desc]
            if isinstance(export_i.desc, Indices.tableidx):
                val = self.tableaddrs[export_i.desc]
            if isinstance(export_i.desc, Indices.memidx):
                val = self.memaddrs[export_i.desc]
            if isinstance(export_i.desc, Indices.globalidx):
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
        f: FuncInst = store.funcs[funcaddr]
        ty = f.type
        assert len(ty.result_types) <= 1
        locals = [stack.pop() for _t in ty.param_types]
        for cast in f.code.locals:
            locals.append(cast(0))
        frame = Frame(locals, f.module)
        stack.push(Activation(len(ty.result_types), frame))
        self.block(store, stack, ty.result_types, f.code.body)
        while self.exec_instruction(store, stack):
            pass

    def exec_expression(self, store: Store, stack: "Stack", expr: WASMExpression):
        self.push_instructions(expr)
        while self.exec_instruction(store, stack):
            pass
        return stack.pop()

    def enter_instruction(self, insts, label: "Label", stack: "Stack"):
        stack.push(label)
        self.push_instructions(insts)

    def exit_instruction(self, stack: "Stack"):
        i = -1
        while True:
            if isinstance(stack.data[i], Value.__args__):
                i -= 1
            else:
                i = abs(i)
                break
        vals = [stack.pop() for _i in range(i)]
        l = stack.pop
        assert isinstance(l, Label)
        for v in vals[::-1]:
            stack.push(v)

        self.push_instructions(l.instr)

    def push_instructions(self, insts: WASMExpression):
        for i in insts[::-1]:
            self._instruction_queue.append(i)

    def exec_instruction(self, store, stack) -> bool:
        if self._instruction_queue:
            inst = self._instruction_queue.pop()
            print(f"{inst.op.id}:", inst.op.mnemonic, f"({debug(inst.imm)})" if inst.imm else "")
            if 0x2 <= inst.op.id <= 0x11:
                if inst.op.id == 0x02:  # block
                    self.block(store, stack, [], [])  # TODO
                # elif inst.op.id == 0x03:  # loop
                #
                # elif inst.op.id == 0x04:  # if
                #
                # elif inst.op.id == 0x05:  # else

                elif inst.op.id == 0x0B:  # end
                    pass
                    # self.exit_instruction(stack)
                # elif inst.op.id == 0x0C:  # br
                #
                # elif inst.op.id == 0x0D:  # br_if
                #
                # elif inst.op.id == 0x0E:  # br_table
                #
                # elif inst.op.id == 0x0F:  # return
                #
                # elif inst.op.id == 0x10:  # call
                #
                # elif inst.op.id == 0x11:  # call_indirect

                else:
                    raise Exception("Unhandled control flow instruction")
            else:
                self.executor.dispatch(inst, store, stack)
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
        self.exit_instruction()  # TODO - this shouldn't happen after exec_expression - not sure if it should happen at all, but idk how else you exit from a block

    def br(self, store: "Store", stack: "Stack", imm: BranchImm):
        raise NotImplementedError("br")

    def br_if(self, store: "Store", stack: "Stack", imm: BranchImm):
        raise NotImplementedError("br_if")

    def br_table(self, store: "Store", stack: "Stack", imm: BranchTableImm):
        raise NotImplementedError("br_table")

    def return_(self, store: "Store", stack: "Stack"):
        raise NotImplementedError("return")

    def call(self, store: "Store", stack: "Stack", imm: CallImm):
        raise NotImplementedError("call")

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
            assert isinstance(self.data[i * -1], t), f"{type(self.data[i * -1])} is not a Value!"
        return True

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
