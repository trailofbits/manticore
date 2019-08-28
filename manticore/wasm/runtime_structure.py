from __future__ import annotations
import typing
import types
import copy
import logging
from dataclasses import dataclass
from .executor import Executor
from collections import deque
from wasm.immtypes import BlockImm, BranchImm, BranchTableImm, CallImm, CallIndirectImm
from .types import (
    U32,
    I32,
    I64,
    F32,
    F64,
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
    debug,
)
from ..core.smtlib import BitVec
from ..core.state import Concretize

logger = logging.getLogger(__name__)
logger.setLevel(logging.INFO)

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

    def __hash__(self):
        return hash((self.funcs, self.tables, self.mems, self.globals))


class AtomicStore(Store):
    def __init__(self, parent: Store):
        self.parent = parent
        self.hash = None  # hash(self.parent)

    def __getstate__(self):
        state = {"parent": self.parent, "hash": self.hash}
        return state

    def __setstate__(self, state):
        self.parent = state["parent"]
        self.hash = state["hash"]

    def __enter__(self):
        return self.parent

    def __exit__(self, exc_type, exc_val, exc_tb):
        pass
        # if exc_val and hash(self.parent) != self.hash:  # TODO - make sure the exception is concretization
        #     logger.warning("An exception occurred _after_ the store was changed. Further execution may be incorrect")


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
        "_block_depths",
    ]

    types: typing.List[FunctionType]
    funcaddrs: typing.List[FuncAddr]
    tableaddrs: typing.List[TableAddr]
    memaddrs: typing.List[MemAddr]
    globaladdrs: typing.List[GlobalAddr]
    exports: typing.List[ExportInst]
    executor: Executor
    _instruction_queue: typing.Deque[Instruction]
    _block_depths: typing.List[int]
    instantiated: bool

    def __init__(self):
        self.types = []
        self.funcaddrs = []
        self.tableaddrs = []
        self.memaddrs = []
        self.globaladdrs = []
        self.exports = []
        self.executor = Executor()
        self._instruction_queue = deque()
        self._block_depths = [0]

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
            "_block_depths": self._block_depths,
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
        self._block_depths = state["_block_depths"]

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
        stack.push(Activation(1, aux_frame))

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
        logger.info("Initialization Complete")

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
            assert isinstance(values[idx], global_i.type.value)
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
        raise RuntimeError("Can't find a function called", name)

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
        locals = [stack.pop() for _t in ty.param_types][::-1]
        if isinstance(f, HostFunc):
            res = list(f.hostcode(*locals))
            logger.info("HostFunc returned", res)
            assert len(res) == len(ty.result_types)
            for r, t in zip(res, ty.result_types):
                stack.push(t.cast(r))
        else:
            for cast in f.code.locals:
                locals.append(cast(0))
            frame = Frame(locals, f.module)
            stack.push(Activation(len(ty.result_types), frame))
            self._block_depths.append(0)
            self.block(store, stack, ty.result_types, f.code.body)

    def exec_expression(self, store: Store, stack: "Stack", expr: WASMExpression):
        self.push_instructions(expr)
        while self.exec_instruction(store, stack):
            pass
        return stack.pop()

    def enter_block(self, insts, label: "Label", stack: "Stack"):
        stack.push(label)
        self._block_depths[-1] += 1
        self.push_instructions(insts)

    def exit_block(self, stack: "AtomicStack"):
        label_idx = stack.find_type(Label)
        if label_idx is not None:
            logger.debug("EXITING BLOCK (FD: %d, BD: %d)", len(self._block_depths), self._block_depths[-1])
            vals = []
            while not isinstance(stack.peek(), Label):
                vals.append(stack.pop())
                assert isinstance(
                    vals[-1], Value.__args__
                ), f"{type(vals[-1])} is not a value or a label"
            label = stack.pop()
            assert isinstance(label, Label), f"Stack contained a {type(label)} instead of a Label"
            self._block_depths[-1] -= 1
            for v in vals[::-1]:
                stack.push(v)

    def exit_function(self, stack: "AtomicStack"):
        if len(self._block_depths) > 1:  # Only if we're in a _real_ function, not initialization
            logger.debug("EXITING FUNCTION (FD: %d, BD: %d)", len(self._block_depths), self._block_depths[-1])
            f = stack.get_frame()
            n = f.arity
            stack.has_type_on_top(Value.__args__, n)
            vals = [stack.pop() for _ in range(n)]
            assert isinstance(stack.peek(), Activation), f"Stack should have an activation on top, instead has {type(stack.peek())}"
            self._block_depths.pop()
            stack.pop()
            for v in vals[::-1]:
                stack.push(v)

    def push_instructions(self, insts: WASMExpression):
        for i in insts[::-1]:
            self._instruction_queue.appendleft(i)

    def look_forward(self, opcode) -> typing.List[Instruction]:
        """
        :param opcode:
        :return:
        """
        out = []
        i = self._instruction_queue.popleft()
        while i.opcode != opcode:
            out.append(i)
            if i.opcode in {0x02, 0x03, 0x04}:
                out += self.look_forward(0x0B)
            if len(self._instruction_queue) == 0:
                raise RuntimeError("Could not find an instruction with opcode " + hex(opcode))
            i = self._instruction_queue.popleft()
        out.append(i)
        return out

    def exec_instruction(self, store: Store, stack: Stack) -> bool:
        ret_type_map = {-1: [I32], -2: [I64], -3: [F32], -4: [F64], -64: []}
        with AtomicStack(stack) as aStack:
            with AtomicStore(store) as aStore:
                if self._instruction_queue:
                    try:
                        inst = self._instruction_queue.popleft()
                        logger.info(
                            "%s: %s (%s)",
                            hex(inst.opcode),
                            inst.mnemonic,
                            debug(inst.imm) if inst.imm else "",
                        )
                        if 0x2 <= inst.opcode <= 0x11:
                            if inst.opcode == 0x02:
                                self.block(
                                    aStore,
                                    aStack,
                                    ret_type_map[inst.imm.sig],
                                    self.look_forward(0x0B),
                                )
                            elif inst.opcode == 0x03:
                                self.loop(aStore, aStack, inst)
                            elif inst.opcode == 0x04:
                                self.if_(aStore, aStack, ret_type_map[inst.imm.sig])
                            elif inst.opcode == 0x05:
                                self.else_(aStore, aStack)
                            elif inst.opcode == 0x0B:
                                self.end(aStore, aStack)
                            elif inst.opcode == 0x0C:
                                self.br(aStore, aStack, inst.imm)
                            elif inst.opcode == 0x0D:
                                self.br_if(aStore, aStack, inst.imm)
                            elif inst.opcode == 0x0E:
                                self.br_table(aStore, aStack, inst.imm)
                            elif inst.opcode == 0x0F:
                                self.return_(aStore, aStack)
                            elif inst.opcode == 0x10:
                                self.call(aStore, aStack, inst.imm)
                            elif inst.opcode == 0x11:
                                self.call_indirect(aStore, aStack, inst.imm)
                            else:
                                raise Exception("Unhandled control flow instruction")
                        else:
                            self.executor.dispatch(inst, aStore, aStack)
                        return True
                    except Concretize as exc:
                        self._instruction_queue.appendleft(inst)
                        raise exc

                elif aStack.find_type(Label):
                    raise RuntimeError("This should never happen")
            # if len(self._block_depths) > 1:
            #     self._block_depths.pop()
            return False

    def block(
        self, store: "Store", stack: "Stack", ret_type: typing.List[ValType], insts: WASMExpression
    ):
        arity = len(ret_type)
        l = Label(arity, [])
        self.enter_block(insts, l, stack)

    def loop(self, store: "Store", stack: "Stack", loop_inst):
        insts = self.look_forward(0x0B)
        l = Label(0, [loop_inst] + insts)
        self.enter_block(insts, l, stack)

    def if_(self, store: "Store", stack: "Stack", ret_type: typing.List[type]):
        stack.has_type_on_top(I32, 1)
        c = stack.pop()
        t_block = self.look_forward(0x05)
        f_block = self.look_forward(0x0B)
        l = Label(len(ret_type), [])
        if c != 0:
            self.enter_block(t_block, l, stack)
        else:
            self.enter_block(f_block, l, stack)

    def else_(self, store: "Store", stack: "Stack"):
        self.exit_block(stack)

    def end(self, store: "Store", stack: "Stack"):
        if self._block_depths[-1] > 0:
            self.exit_block(stack)
        if self._block_depths[-1] == 0:
            self.exit_function(stack)

    def br(self, store: "Store", stack: "Stack", imm: BranchImm):
        raise NotImplementedError("br")

    def br_if(self, store: "Store", stack: "Stack", imm: BranchImm):
        stack.has_type_on_top(I32, 1)
        c = stack.pop()
        if c != 0:
            self.br(store, stack, imm)

    def br_table(self, store: "Store", stack: "Stack", imm: BranchTableImm):
        raise NotImplementedError("br_table")

    def return_(self, store: "Store", stack: "Stack"):
        f = stack.get_frame()
        n = f.arity
        stack.has_type_on_top(Value.__args__, n)
        ret = [stack.pop() for _i in range(n)]
        while not isinstance(stack.peek(), (Activation, Frame)):
            stack.pop()
        assert stack.peek() == f
        stack.pop()
        self._block_depths.pop()
        for r in ret[::-1]:
            stack.push(r)
        self.look_forward(0x0B)  # Discard the rest of the function

    def call(self, store: "Store", stack: "Stack", imm: CallImm):
        f = stack.get_frame()
        assert imm.function_index in range(len(f.frame.module.funcaddrs))
        a = f.frame.module.funcaddrs[imm.function_index]
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
        if isinstance(val, list):
            raise RuntimeError("Don't push lists")
        logger.debug("+%d %s (%s)", len(self.data), val, type(val))
        self.data.append(val)

    def pop(self) -> typing.Union[Value, Label, Activation]:
        logger.debug("-%d %s (%s)", len(self.data) - 1, self.peek(), type(self.peek()))
        return self.data.pop()

    def peek(self):
        return self.data[-1]

    def empty(self):
        return len(self.data) == 0

    def has_type_on_top(self, t: type, n: int):
        for i in range(1, n + 1):
            assert isinstance(
                self.data[i * -1], (t, BitVec)
            ), f"{type(self.data[i * -1])} is not an {t}!"
        return True

    def find_type(self, t: type):
        for idx, v in enumerate(reversed(self.data)):
            if isinstance(v, t):
                return -1 * idx
        return None

    def get_frame(self) -> Activation:
        for item in reversed(self.data):
            if isinstance(item, Activation):
                return item


class AtomicStack(Stack):
    """
    Allows for the rolling-back of the stack in the event of a concretization exception. Inherits from Stack so that the types will be correct, but never calls `super`
    TODO - make this more efficient by eliminating the full copy and instead doing a CoW-esque thing
    """

    def __init__(self, parent: Stack):
        self.parent = parent
        self.copy = copy.copy(self.parent.data)

    def __getstate__(self):
        state = {"parent": self.parent, "copy": self.copy}
        return state

    def __setstate__(self, state):
        self.parent = state["parent"]
        self.copy = state["copy"]

    def __enter__(self):
        return self

    def __exit__(self, exc_type, exc_val, exc_tb):
        if exc_val and isinstance(exc_val, Concretize):
            logger.info("Exception occurred, not applying stack changes")
            self.parent.data = self.copy
        else:
            pass

    def push(self, val: typing.Union[Value, Label, Activation]) -> None:
        self.parent.push(val)

    def pop(self) -> typing.Union[Value, Label, Activation]:
        return self.parent.pop()

    def peek(self):
        return self.parent.peek()

    def empty(self):
        return self.parent.empty()

    def has_type_on_top(self, t: type, n: int):
        return self.parent.has_type_on_top(t, n)

    def find_type(self, t: type):
        return self.parent.find_type(t)

    def get_frame(self) -> Activation:
        return self.parent.get_frame()


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
