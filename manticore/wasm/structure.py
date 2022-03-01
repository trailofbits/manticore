# from __future__ import annotations
import typing
import types
import logging
from dataclasses import dataclass
from .executor import Executor
from collections import deque
from math import ceil
from .types import (
    BranchImm,
    BranchTableImm,
    CallImm,
    CallIndirectImm,
    ConcretizeStack,
    convert_instructions,
    debug,
    F32,
    F64,
    FuncIdx,
    FunctionType,
    GlobalIdx,
    GlobalType,
    I32,
    I64,
    Instruction,
    LimitType,
    MemIdx,
    MemoryType,
    MissingExportException,
    Name,
    NonExistentFunctionCallTrap,
    OutOfBoundsMemoryTrap,
    OverflowDivisionTrap,
    TableIdx,
    TableType,
    Trap,
    TypeIdx,
    TypeMismatchTrap,
    U32,
    ValType,
    Value,
    Value_t,
    WASMExpression,
    ZeroDivisionTrap,
)
from .state import State
from ..core.smtlib import BitVec, Bool, issymbolic, Operators, Expression
from ..core.state import Concretize
from ..utils.event import Eventful
from ..utils import config

from wasm import decode_module, Section
from wasm.wasmtypes import (
    SEC_TYPE,
    SEC_IMPORT,
    SEC_FUNCTION,
    SEC_TABLE,
    SEC_MEMORY,
    SEC_GLOBAL,
    SEC_EXPORT,
    SEC_START,
    SEC_ELEMENT,
    SEC_CODE,
    SEC_DATA,
    SEC_UNK,
)

from ..core.smtlib.solver import SelectedSolver


logger = logging.getLogger(__name__)
# logger.setLevel(logging.DEBUG)

consts = config.get_group("wasm")
consts.add(
    "decode_names",
    default=False,
    description="Should Manticore attempt to decode custom name sections",
)

#: Size of a standard WASM memory page
PAGESIZE = 2**16


# Wrappers around integers that we use for indexing the store.
class Addr(int):
    pass


class FuncAddr(Addr):
    pass


class TableAddr(Addr):
    pass


class MemAddr(Addr):
    pass


class GlobalAddr(Addr):
    pass


ExternVal = typing.Union[FuncAddr, TableAddr, MemAddr, GlobalAddr]
FuncElem = typing.Optional[FuncAddr]

ExportDesc = typing.Union[FuncIdx, TableIdx, MemIdx, GlobalIdx]
ImportDesc = typing.Union[TypeIdx, TableType, MemoryType, GlobalType]


@dataclass
class Function:
    """
    A WASM Function

    https://www.w3.org/TR/wasm-core-1/#functions%E2%91%A0
    """

    type: TypeIdx  #: The index of a type defined in the module that corresponds to this function's type signature
    locals: typing.List[ValType]  #: Vector of mutable local variables (and their types)
    body: WASMExpression  #: Sequence of WASM instructions, should leave the appropriate type on the stack

    def allocate(self, store: "Store", module: "ModuleInstance") -> FuncAddr:
        """
        https://www.w3.org/TR/wasm-core-1/#functions%E2%91%A5

        :param store: Destination Store that we'll insert this Function into after allocation
        :param module: The module containing the type referenced by self.type
        :return: The address of this within `store`
        """
        a = FuncAddr(len(store.funcs))
        store.funcs.append(FuncInst(module.types[self.type], module, self))
        return a


@dataclass
class Table:
    """
    Vector of opaque values of type self.type

    https://www.w3.org/TR/wasm-core-1/#tables%E2%91%A0
    """

    type: TableType  #: union of a limit and a type (currently only supports funcref)s

    def allocate(self, store: "Store") -> TableAddr:
        """
        https://www.w3.org/TR/wasm-core-1/#tables%E2%91%A5

        :param store: Destination Store that we'll insert this Table into after allocation
        :return: The address of this within `store`
        """
        a = TableAddr(len(store.tables))
        store.tables.append(
            TableInst([None for _i in range(self.type.limits.min)], self.type.limits.max)
        )
        return a


@dataclass
class Memory:
    """
    Big chunk o' raw bytes

    https://www.w3.org/TR/wasm-core-1/#memories%E2%91%A0
    """

    type: MemoryType  #: secretly a LimitType that specifies how big or small the memory can be

    def allocate(self, store: "Store") -> MemAddr:
        """
        https://www.w3.org/TR/wasm-core-1/#memories%E2%91%A5

        :param store: Destination Store that we'll insert this Memory into after allocation
        :return: The address of this within `store`
        """
        a = MemAddr(len(store.mems))
        store.mems.append(MemInst([0x0] * self.type.min * 64 * 1024, self.type.max))
        return a


@dataclass
class Global:
    """
    A global variable of a given type

    https://www.w3.org/TR/wasm-core-1/#globals%E2%91%A0
    """

    type: GlobalType  #: The type of the variable
    init: WASMExpression  #: A (constant) sequence of WASM instructions that calculates the value for the global

    def allocate(self, store: "Store", val: Value) -> GlobalAddr:
        """
        https://www.w3.org/TR/wasm-core-1/#globals%E2%91%A5

        :param store: Destination Store that we'll insert this Global into after allocation
        :param val: The initial value of the new global
        :return: The address of this within `store`
        """
        a = GlobalAddr(len(store.globals))
        store.globals.append(GlobalInst(val, self.type.mut))
        return a


@dataclass
class Elem:
    """
    List of functions to initialize part of a table

    https://www.w3.org/TR/wasm-core-1/#element-segments%E2%91%A0
    """

    table: TableIdx  #: Which table to initialize
    offset: WASMExpression  #: WASM instructions that calculate an offset to add to the table index
    init: typing.List[FuncIdx]  #: list of function indices that get copied into the table


@dataclass
class Data:
    """
    Vector of bytes that initializes part of a memory

    https://www.w3.org/TR/wasm-core-1/#data-segments%E2%91%A0
    """

    data: MemIdx  #: Which memory to put the data in. Currently only supports 0
    offset: WASMExpression  #: WASM instructions that calculate offset into the memory
    init: typing.List[int]  #: List of bytes to copy into the memory


@dataclass
class Import:
    """
    Something imported from another module (or the environment) that we need to instantiate a module

    https://www.w3.org/TR/wasm-core-1/#imports%E2%91%A0
    """

    module: Name  #: The name of the module we're importing from
    name: Name  #: The name of the thing we're importing
    desc: ImportDesc  #: Specifies whether this is a function, table, memory, or global


@dataclass
class Export:
    """
    Something the module exposes to the outside world once it's been instantiated

    https://www.w3.org/TR/wasm-core-1/#exports%E2%91%A0
    """

    name: Name  #: The name of the thing we're exporting
    desc: ExportDesc  #: Whether this is a function, table, memory, or global


def strip_quotes(rough_name: str) -> Name:
    """
    For some reason, the parser returns the function names with quotes around them

    :param rough_name:
    :return:
    """
    return Name(rough_name[1:-1])


class Module:
    """
    Internal representation of a WASM Module
    """

    __slots__ = [
        "types",
        "funcs",
        "tables",
        "mems",
        "globals",
        "elem",
        "data",
        "start",
        "imports",
        "exports",
        "function_names",
        "local_names",
        "_raw",
    ]
    _raw: bytes

    def __init__(self):
        self.types: typing.List[FunctionType] = []
        self.funcs: typing.List[Function] = []
        self.tables: typing.List[Table] = []
        self.mems: typing.List[Memory] = []
        self.globals: typing.List[Global] = []
        self.elem: typing.List[Elem] = []
        self.data: typing.List[Data] = []
        self.start: typing.Optional[
            FuncIdx
        ] = None  #: https://www.w3.org/TR/wasm-core-1/#start-function%E2%91%A0
        self.imports: typing.List[Import] = []
        self.exports: typing.List[Export] = []
        self.function_names: typing.Dict[FuncAddr, str] = {}
        self.local_names: typing.Dict[FuncAddr, typing.Dict[int, str]] = {}

    def __getstate__(self):
        state = {
            "types": self.types,
            "funcs": self.funcs,
            "tables": self.tables,
            "mems": self.mems,
            "globals": self.globals,
            "elem": self.elem,
            "data": self.data,
            "start": self.start,
            "imports": self.imports,
            "exports": self.exports,
            "function_names": self.function_names,
            "local_names": self.local_names,
            "_raw": self._raw,
        }
        return state

    def __setstate__(self, state):
        self.types = state["types"]
        self.funcs = state["funcs"]
        self.tables = state["tables"]
        self.mems = state["mems"]
        self.globals = state["globals"]
        self.elem = state["elem"]
        self.data = state["data"]
        self.start = state["start"]
        self.imports = state["imports"]
        self.exports = state["exports"]
        self.function_names = state["function_names"]
        self.local_names = state["local_names"]
        self._raw = state["_raw"]

    def get_funcnames(self) -> typing.List[Name]:
        return [e.name for e in self.exports if isinstance(e.desc, FuncIdx)]

    @classmethod
    def load(cls, filename: str):
        """
        Converts a WASM module in binary format into Python types that Manticore can understand

        :param filename: name of the WASM module
        :return: Module
        """
        type_map = {-16: FunctionType, -4: F64, -3: F32, -2: I64, -1: I32}

        m: Module = cls()
        with open(filename, "rb") as wasm_file:
            m._raw = wasm_file.read()

        # Test modules break name subsection decoding. TODO: Find a better WASM importer
        module_iter = decode_module(m._raw, decode_name_subsections=consts.decode_names)
        _header = next(module_iter)
        section: Section
        # Parse the sections from the WASM module into internal types. For each section, the code usually resembles:
        # `module.<something>.append(<InstanceOfSomething>(data, from, binary, module))`
        for section, section_data in module_iter:
            sec_id = getattr(section_data, "id", SEC_UNK)
            if sec_id == SEC_TYPE:  # https://www.w3.org/TR/wasm-core-1/#type-section%E2%91%A0
                for ft in section_data.payload.entries:
                    m.types.append(
                        FunctionType(
                            [type_map[p_type] for p_type in ft.param_types],
                            [type_map[ft.return_type] for _i in range(ft.return_count)],
                        )
                    )
            elif sec_id == SEC_IMPORT:  # https://www.w3.org/TR/wasm-core-1/#import-section%E2%91%A0
                for i in section_data.payload.entries:
                    ty_map = i.get_decoder_meta()["types"]
                    mod_name = strip_quotes(ty_map["module_str"].to_string(i.module_str))
                    field_name = strip_quotes(ty_map["field_str"].to_string(i.field_str))
                    if i.kind == 0:
                        m.imports.append(Import(mod_name, field_name, TypeIdx(i.type.type)))

                    elif i.kind == 1:
                        m.imports.append(
                            Import(
                                mod_name,
                                field_name,
                                TableType(
                                    LimitType(i.type.limits.initial, i.type.limits.maximum),
                                    type_map[i.type.element_type],
                                ),
                            )
                        )

                    elif i.kind == 2:
                        m.imports.append(
                            Import(
                                mod_name,
                                field_name,
                                MemoryType(i.type.limits.initial, i.type.limits.maximum),
                            )
                        )

                    elif i.kind == 3:
                        m.imports.append(
                            Import(
                                mod_name,
                                field_name,
                                GlobalType(bool(i.type.mutability), type_map[i.type.content_type]),
                            )
                        )

                    else:
                        raise RuntimeError("Can't decode kind field of:", i.kind)

            elif (
                sec_id == SEC_FUNCTION
            ):  # https://www.w3.org/TR/wasm-core-1/#function-section%E2%91%A0
                for f in section_data.payload.types:
                    m.funcs.append(
                        Function(TypeIdx(f), [], [])
                    )  # The expressions and locals are stored in the code section
            elif sec_id == SEC_TABLE:  # https://www.w3.org/TR/wasm-core-1/#table-section%E2%91%A0
                for t in section_data.payload.entries:
                    m.tables.append(
                        Table(
                            TableType(LimitType(t.limits.initial, t.limits.maximum), FunctionType)
                        )
                    )
            elif sec_id == SEC_MEMORY:  # https://www.w3.org/TR/wasm-core-1/#memory-section%E2%91%A0
                for mem in section_data.payload.entries:
                    m.mems.append(Memory(LimitType(mem.limits.initial, mem.limits.maximum)))
            elif sec_id == SEC_GLOBAL:  # https://www.w3.org/TR/wasm-core-1/#global-section%E2%91%A0
                for g in section_data.payload.globals:
                    m.globals.append(
                        Global(
                            GlobalType(g.type.mutability, type_map[g.type.content_type]),
                            convert_instructions(g.init),
                        )
                    )
            elif sec_id == SEC_EXPORT:  # https://www.w3.org/TR/wasm-core-1/#export-section%E2%91%A0
                mapping = (FuncIdx, TableIdx, MemIdx, GlobalIdx)
                for e in section_data.payload.entries:
                    ty = e.get_decoder_meta()["types"]["field_str"]
                    m.exports.append(
                        Export(strip_quotes(ty.to_string(e.field_str)), mapping[e.kind](e.index))
                    )
            elif sec_id == SEC_START:  # https://www.w3.org/TR/wasm-core-1/#start-section%E2%91%A0
                m.start = FuncIdx(section_data.payload.index)
            elif (
                sec_id == SEC_ELEMENT
            ):  # https://www.w3.org/TR/wasm-core-1/#element-section%E2%91%A0
                for e in section_data.payload.entries:
                    m.elem.append(
                        Elem(
                            TableIdx(e.index),
                            convert_instructions(e.offset),
                            [FuncIdx(i) for i in e.elems],
                        )
                    )
            elif sec_id == SEC_CODE:  # https://www.w3.org/TR/wasm-core-1/#code-section%E2%91%A0
                for idx, c in enumerate(section_data.payload.bodies):
                    m.funcs[idx].locals = [
                        type_map[e.type] for e in c.locals for _i in range(e.count)
                    ]
                    m.funcs[idx].body = convert_instructions(c.code)
            elif sec_id == SEC_DATA:  # https://www.w3.org/TR/wasm-core-1/#data-section%E2%91%A0
                for d in section_data.payload.entries:
                    m.data.append(
                        Data(MemIdx(d.index), convert_instructions(d.offset), d.data.tolist())
                    )
            elif sec_id == SEC_UNK:
                # WASM module renders all types as `GeneratedStructureData` so `isinstance` doesn't work :(
                if (
                    hasattr(section, "name_type")
                    and hasattr(section, "payload_len")
                    and hasattr(section, "payload")
                ):
                    # https://webassembly.github.io/spec/core/appendix/custom.html#subsections
                    name_type = section_data.name_type
                    if name_type == 0:  # module name
                        pass
                    elif name_type == 1:  # function names
                        for n in section_data.payload.names:
                            ty = n.get_decoder_meta()["types"]["name_str"]
                            m.function_names[FuncAddr(n.index)] = strip_quotes(
                                ty.to_string(n.name_str)
                            )
                    elif name_type == 2:  # local variable names
                        for func in section_data.payload.funcs:
                            func_idx = func.index
                            for n in func.local_map.names:
                                ty = n.get_decoder_meta()["types"]["name_str"]
                                m.local_names.setdefault(FuncAddr(func_idx), {})[
                                    n.index
                                ] = strip_quotes(ty.to_string(n.name_str))
                else:
                    logger.info("Encountered unknown section")
                    # TODO - other custom sections (https://www.w3.org/TR/wasm-core-1/#custom-section%E2%91%A0)

        return m


@dataclass
class ProtoFuncInst:
    """
    Groups FuncInst and HostFuncInst into the same category
    """

    type: FunctionType  #: The type signature of this function


@dataclass
class TableInst:
    """
    Runtime representation of a table. Remember that the Table type stores the type of the data contained in the table
    and basically nothing else, so if you're dealing with a table at runtime, it's probably a TableInst. The WASM
    spec has a lot of similar-sounding names for different versions of one thing.

    https://www.w3.org/TR/wasm-core-1/#table-instances%E2%91%A0
    """

    #: A list of FuncAddrs (any of which can be None) that point to funcs in the Store
    elem: typing.List[FuncElem]
    max: typing.Optional[U32]  #: Optional maximum size of the table


class MemInst(Eventful):
    """
    Runtime representation of a memory. As with tables, if you're dealing with a memory at runtime, it's probably a
    MemInst. Currently doesn't support any sort of symbolic indexing, although you can read and write symbolic bytes
    using smtlib. There's a minor quirk where uninitialized data is stored as bytes, but smtlib tries to convert
    concrete data into ints. That can cause problems if you try to read from the memory directly (without using smtlib)
    but shouldn't break any of the built-in WASM instruction implementations.

    Memory in WASM is broken up into 65536-byte pages. All pages behave the same way, but note that operations that
    deal with memory size do so in terms of pages, not bytes.

    TODO: We should implement some kind of symbolic memory model

    https://www.w3.org/TR/wasm-core-1/#memory-instances%E2%91%A0
    """

    _published_events = {"write_memory", "read_memory"}

    _pages: typing.Dict[int, typing.List[int]]
    max: typing.Optional[U32]  #: Optional maximum number of pages the memory can contain
    _current_size: int  # Tracks the theoretical size of the memory instance, including unmapped pages

    def __init__(self, starting_data, max=None, *args, **kwargs):
        super().__init__(*args, **kwargs)
        self._current_size = ceil(len(starting_data) / PAGESIZE)
        self.max = max
        self._pages = {}

        chunked = [starting_data[i : i + PAGESIZE] for i in range(0, len(starting_data), PAGESIZE)]
        for idx, page in enumerate(chunked):
            if len(page) < PAGESIZE:
                page.extend([0x0] * (PAGESIZE - len(page)))
            self._pages[idx] = page

    def __getstate__(self):
        state = super().__getstate__()
        state["pages"] = self._pages
        state["max"] = self.max
        state["current"] = self._current_size
        return state

    def __setstate__(self, state):
        super().__setstate__(state)
        self._pages = state["pages"]
        self.max = state["max"]
        self._current_size = state["current"]

    def __contains__(self, item):
        return item in range(self.npages * PAGESIZE)

    def _check_initialize_index(self, memidx):
        page = memidx // PAGESIZE
        if page not in range(self.npages):
            raise OutOfBoundsMemoryTrap(memidx)
        if page not in self._pages:
            self._pages[page] = [0x0] * PAGESIZE
        return divmod(memidx, PAGESIZE)

    def _read_byte(self, addr):
        page, idx = self._check_initialize_index(addr)
        return self._pages[page][idx]

    def _write_byte(self, addr, val):
        page, idx = self._check_initialize_index(addr)
        self._pages[page][idx] = val

    @property
    def npages(self):
        return self._current_size

    def grow(self, n: int) -> bool:
        """
        Adds n blank pages to the current memory

        See: https://www.w3.org/TR/wasm-core-1/#grow-mem

        :param n: The number of pages to attempt to add
        :return: True if the operation succeeded, otherwise False
        """
        ln = n + self.npages
        if ln > (PAGESIZE):
            return False
        if self.max is not None:
            if ln > self.max:
                return False
        self._current_size = ln
        return True

    def write_int(self, base: int, expression: typing.Union[Expression, int], size: int = 32):
        """
        Writes an integer into memory.

        :param base: Index to write at
        :param expression: integer to write
        :param size: Optional size of the integer
        """
        b = [
            Operators.CHR(Operators.EXTRACT(expression, offset, 8)) for offset in range(0, size, 8)
        ]
        self.write_bytes(base, b)

    def write_bytes(
        self, base: int, data: typing.Union[str, typing.Sequence[int], typing.Sequence[bytes]]
    ):
        """
        Writes  a stream of bytes into memory

        :param base: Index to start writing at
        :param data: Data to write
        """
        self._publish("will_write_memory", base, base + len(data), data)
        for idx, v in enumerate(data):
            self._write_byte(base + idx, v)
        self._publish("did_write_memory", base, data)

    def read_int(self, base: int, size: int = 32) -> int:
        """
        Reads bytes from memory and combines them into an int

        :param base: Address to read the int from
        :param size: Size of the int (in bits)
        :return: The int in question
        """
        return Operators.CONCAT(
            size, *map(Operators.ORD, reversed(self.read_bytes(base, size // 8)))
        )

    def read_bytes(self, base: int, size: int) -> typing.List[typing.Union[int, bytes]]:
        """
        Reads bytes from memory

        :param base: Address to read from
        :param size: number of bytes to read
        :return: List of bytes
        """
        self._publish("will_read_memory", base, base + size)
        d = [self._read_byte(i) for i in range(base, base + size)]
        self._publish("did_read_memory", base, d)
        return d

    def dump(self):
        return self.read_bytes(0, self._current_size * PAGESIZE)


@dataclass
class GlobalInst:
    """
    Instance of a global variable. Stores the value (calculated from evaluating a Global.init) and the mutable flag
    (taken from GlobalType.mut)

    https://www.w3.org/TR/wasm-core-1/#global-instances%E2%91%A0
    """

    value: Value  #: The actual value of this global
    mut: bool  #: Whether the global can be modified


@dataclass
class ExportInst:
    """
    Runtime representation of any thing that can be exported

    https://www.w3.org/TR/wasm-core-1/#export-instances%E2%91%A0
    """

    name: Name  #: The name to export under
    value: ExternVal  #: FuncAddr, TableAddr, MemAddr, or GlobalAddr


class Store:
    """
    Implementation of the WASM store. Nothing fancy here, just collects lists of functions, tables, memories, and
    globals. Because the store is not atomic, instructions SHOULD NOT make changes to the Store or any of its contents
    (including memories and global variables) before raising a Concretize exception.

    https://www.w3.org/TR/wasm-core-1/#store%E2%91%A0
    """

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


def _eval_maybe_symbolic(state, expression) -> bool:
    if issymbolic(expression):
        return state.must_be_true(expression)
    return True if expression else False


class ModuleInstance(Eventful):
    """
    Runtime instance of a module. Stores function types, list of addresses within the store, and exports. In this
    implementation, it's also responsible for managing the instruction queue and executing control-flow instructions.

    https://www.w3.org/TR/wasm-core-1/#module-instances%E2%91%A0
    """

    __slots__ = [
        "types",
        "funcaddrs",
        "tableaddrs",
        "memaddrs",
        "globaladdrs",
        "exports",
        "export_map",
        "executor",
        "function_names",
        "local_names",
        "_instruction_queue",
        "_block_depths",
        "_advice",
        "_state",
    ]

    _published_events = {"execute_instruction", "call_hostfunc", "exec_expression", "raise_trap"}

    #: Stores the type signatures of all the functions
    types: typing.List[FunctionType]
    #: Stores the *indices* of functions within the store
    funcaddrs: typing.List[FuncAddr]
    #: Stores the indices of tables
    tableaddrs: typing.List[TableAddr]
    #: Stores the indices of memories (at time of writing, WASM only allows one memory)
    memaddrs: typing.List[MemAddr]
    #: Stores the indices of globals
    globaladdrs: typing.List[GlobalAddr]
    #: Stores records of everything exported by this module
    exports: typing.List[ExportInst]
    #: Maps the names of exports to their index in the list of exports
    export_map: typing.Dict[str, int]
    #: Contains instruction implementations for all non-control-flow instructions
    executor: Executor
    #: Stores names of store functions, if available
    function_names: typing.Dict[FuncAddr, str]
    #: Stores names of local variables, if available
    local_names: typing.Dict[FuncAddr, typing.Dict[int, str]]
    #: Stores the unpacked sequence of instructions in the order they should be executed
    _instruction_queue: typing.Deque[Instruction]
    #: Keeps track of the current call depth, both for functions and for code blocks. Each function call is represented
    # by appending another 0 to the list, and each code block is represented by incrementing the digit at the end of the
    # list. This is necessary because we unroll the WASM S-Expressions (nested execution trees) into a single
    # instruction queue, so the meaning of an `end` instruction could be otherwise ambiguous. Loosely put, the sum of
    # all the digits in this list is the number of `end` instructions we need to see before execution is finished.
    _block_depths: typing.List[int]
    #: Stickies the advice conditions before each instruction.
    _advice: typing.Optional[typing.List[bool]]
    #: Prevents the user from invoking functions before instantiation
    instantiated: bool
    #: Stickies the current state before each instruction
    _state: State

    def __init__(self, constraints=None):
        self.types = []
        self.funcaddrs = []
        self.tableaddrs = []
        self.memaddrs = []
        self.globaladdrs = []
        self.exports = []
        self.export_map = {}
        self.executor = Executor()
        self.function_names = {}
        self.local_names = {}
        self._instruction_queue = deque()
        self._block_depths = [0]
        self._advice = None
        self._state = None

        super().__init__()

    def __getstate__(self):
        state = super().__getstate__()
        state.update(
            {
                "types": self.types,
                "funcaddrs": self.funcaddrs,
                "tableaddrs": self.tableaddrs,
                "memaddrs": self.memaddrs,
                "globaladdrs": self.globaladdrs,
                "exports": self.exports,
                "export_map": self.export_map,
                "executor": self.executor,
                "function_names": self.function_names,
                "local_names": self.local_names,
                "_instruction_queue": self._instruction_queue,
                "_block_depths": self._block_depths,
            }
        )
        return state

    def __setstate__(self, state):
        self.types = state["types"]
        self.funcaddrs = state["funcaddrs"]
        self.tableaddrs = state["tableaddrs"]
        self.memaddrs = state["memaddrs"]
        self.globaladdrs = state["globaladdrs"]
        self.exports = state["exports"]
        self.export_map = state["export_map"]
        self.executor = state["executor"]
        self.function_names = state["function_names"]
        self.local_names = state["local_names"]
        self._instruction_queue = state["_instruction_queue"]
        self._block_depths = state["_block_depths"]
        self._advice = None
        self._state = None
        super().__setstate__(state)

    def reset_internal(self):
        """
        Empties the instruction queue and clears the block depths
        """
        self._instruction_queue.clear()
        self._block_depths = [0]

    def instantiate(
        self,
        store: Store,
        module: "Module",
        extern_vals: typing.List[ExternVal],
        exec_start: bool = False,
    ):
        """
        Type checks the module, evaluates globals, performs allocation, and puts the element and data sections into
        their proper places. Optionally calls the start function _outside_ of a symbolic context if exec_start is true.

        https://www.w3.org/TR/wasm-core-1/#instantiation%E2%91%A1

        :param store: The store to place the allocated contents in
        :param module: The WASM Module to instantiate in this instance
        :param extern_vals: Imports needed to instantiate the module
        :param exec_start: whether or not to execute the start section (if present)
        """
        # #1 Assert: module is valid
        assert module  # close enough

        # TODO: #2 Assert: module is valid with external types _externtype_ classifying its imports.
        # for ext in module.imports:
        #     assert isinstance(ext, ExternType.__args__)

        # #3 Assert the same number of imports and external values
        assert len(module.imports) == len(
            extern_vals
        ), f"Expected {len(module.imports)} imports, got {len(extern_vals)}"

        # #4 TODO

        # #5 - evaluate globals
        stack = Stack()

        aux_mod = ModuleInstance()
        aux_mod.globaladdrs = [i for i in extern_vals if isinstance(i, GlobalAddr)]
        aux_frame = Frame([], aux_mod)
        stack.push(Activation(1, aux_frame))

        vals = [self.exec_expression(store, stack, gb.init) for gb in module.globals]

        last_frame = stack.pop()
        assert isinstance(last_frame, Activation)
        assert last_frame.frame == aux_frame

        # #6, #7, #8 - Allocate all the things
        self.allocate(store, module, extern_vals, vals)
        f = Frame(locals=[], module=self)
        stack.push(Activation(0, f))

        # #9 & #13 - emplace element sections into tables
        for elem in module.elem:
            eoval = self.exec_expression(store, stack, elem.offset)
            assert isinstance(eoval, I32)
            assert elem.table in range(len(self.tableaddrs))
            tableaddr: TableAddr = self.tableaddrs[elem.table]
            assert tableaddr in range(len(store.tables))
            tableinst: TableInst = store.tables[tableaddr]
            eend = eoval + len(elem.init)
            assert eend <= len(tableinst.elem)

            func_idx: FuncIdx
            for j, func_idx in enumerate(elem.init):
                assert func_idx in range(len(self.funcaddrs))
                funcaddr = self.funcaddrs[func_idx]
                tableinst.elem[eoval + j] = funcaddr

        # #10 & #14 - emplace data sections into memory
        for data in module.data:
            doval = self.exec_expression(store, stack, data.offset)
            assert isinstance(doval, I32), f"{type(doval)} is not an I32"
            assert data.data in range(len(self.memaddrs))
            memaddr = self.memaddrs[data.data]
            assert memaddr in range(len(store.mems))
            meminst = store.mems[memaddr]
            dend = doval + len(data.init)
            assert dend <= meminst.npages * (PAGESIZE)

            meminst.write_bytes(doval, data.init)

        # #11 & #12
        last_frame = stack.pop()
        assert isinstance(last_frame, Activation)
        assert last_frame.frame == f

        # #15 run start function
        if module.start is not None:
            assert module.start in range(len(self.funcaddrs))
            funcaddr = self.funcaddrs[module.start]
            assert funcaddr in range(len(store.funcs))
            self.invoke(stack, self.funcaddrs[module.start], store, [])
            if exec_start:
                stack.push(self.exec_expression(store, stack, []))
        logger.info("Initialization Complete")

    def allocate(
        self,
        store: Store,
        module: "Module",
        extern_vals: typing.List[ExternVal],
        values: typing.List[Value],
    ):
        """
        Inserts imports into the store, then creates and inserts function instances, table instances, memory instances,
        global instances, and export instances.

        https://www.w3.org/TR/wasm-core-1/#allocation%E2%91%A0
        https://www.w3.org/TR/wasm-core-1/#modules%E2%91%A6

        :param store: The Store to put all of the allocated subcomponents in
        :param module: Tne Module containing all the items to allocate
        :param extern_vals: Imported values
        :param values: precalculated global values
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

        for func in module.funcs:
            addr = func.allocate(store, self)
            self.funcaddrs.append(addr)
            name = module.function_names.get(addr, None)
            if name:
                self.function_names[addr] = name
            local_map = module.local_names.get(addr, None)
            if local_map:
                self.local_names[addr] = local_map.copy()
        for table_i in module.tables:
            self.tableaddrs.append(table_i.allocate(store))
        for memory_i in module.mems:
            self.memaddrs.append(memory_i.allocate(store))
        for idx, global_i in enumerate(module.globals):
            assert isinstance(values[idx], global_i.type.value)
            self.globaladdrs.append(global_i.allocate(store, values[idx]))
        for idx, export_i in enumerate(module.exports):
            if isinstance(export_i.desc, FuncIdx):
                self.exports.append(ExportInst(export_i.name, self.funcaddrs[export_i.desc]))
            elif isinstance(export_i.desc, TableIdx):
                self.exports.append(ExportInst(export_i.name, self.tableaddrs[export_i.desc]))
            elif isinstance(export_i.desc, MemIdx):
                self.exports.append(ExportInst(export_i.name, self.memaddrs[export_i.desc]))
            elif isinstance(export_i.desc, GlobalIdx):
                self.exports.append(ExportInst(export_i.name, self.globaladdrs[export_i.desc]))
            else:
                raise RuntimeError("Export desc wasn't a function, table, memory, or global")
            self.export_map[export_i.name] = len(self.exports) - 1

    def invoke_by_name(self, name: str, stack, store, argv):
        """
        Iterates over the exports, attempts to find the function specified by `name`. Calls `invoke` with its FuncAddr,
        passing argv

        :param name: Name of the function to look for
        :param argv: Arguments to pass to the function. Can be BitVecs or Values
        """
        for export in self.exports:
            if export.name == name and isinstance(export.value, FuncAddr):
                return self.invoke(stack, export.value, store, argv)
        raise RuntimeError("Can't find a function called", name)

    def invoke(self, stack: "Stack", funcaddr: FuncAddr, store: Store, argv: typing.List[Value]):
        """
        Invocation wrapper. Checks the function type, pushes the args to the stack, and calls _invoke_inner.
        Unclear why the spec separates the two procedures, but I've tried to implement it as close to verbatim
        as possible.

        Note that this doesn't actually _run_ any code. It just sets up the instruction queue so that when you call
        `exec_instruction, it'll actually have instructions to execute.

        https://www.w3.org/TR/wasm-core-1/#invocation%E2%91%A1

        :param funcaddr: Address (in Store) of the function to call
        :param argv: Arguments to pass to the function. Can be BitVecs or Values
        """
        assert funcaddr in range(len(store.funcs))
        funcinst = store.funcs[funcaddr]
        ty = funcinst.type
        assert len(ty.param_types) == len(
            argv
        ), f"Function {funcaddr} expects {len(ty.param_types)} arguments"
        # for t, v in zip(ty.param_types, argv):
        #     assert type(v) == type(t)

        # Create dummy frame, which is required by the spec but doesn't serve any obvious purpose. It also never
        # gets popped.
        dummy_frame = Frame([], ModuleInstance())
        stack.push(
            dummy_frame  # type: ignore # This isn't an activation/label/value, but we'll let it slide
        )
        for v in argv:
            stack.push(v)

        # https://www.w3.org/TR/wasm-core-1/#exec-invoke
        self._invoke_inner(stack, funcaddr, store)

        # In the spec, once the function has returned, you pop the returns from the stack and return them to the
        # caller. Since Manticore executes functions via the `run` method (ie separately from invocation), we don't
        # do that here.

    def _invoke_inner(self, stack: "Stack", funcaddr: FuncAddr, store: Store):
        """
        Invokes the function at address funcaddr. Validates the function type, sets up the Activation with the local
        variables, and executes the function. If the function is a HostFunc (native code), it executes it blindly and
        pushes the return values to the stack. If it's a WASM function, it enters the outermost code block.

        https://www.w3.org/TR/wasm-core-1/#exec-invoke

        :param stack: The current stack, to use for execution
        :param funcaddr: The address of the function to invoke
        :param store: The current store, to use for execution
        """
        assert funcaddr in range(len(store.funcs))
        f: ProtoFuncInst = store.funcs[funcaddr]
        ty = f.type
        assert len(ty.result_types) <= 1
        local_vars: typing.List[Value] = []
        for v in [stack.pop() for _ in ty.param_types][::-1]:
            assert not isinstance(v, (Label, Activation))
            local_vars.append(v)

        name = self.function_names.get(funcaddr, f"Func{funcaddr}")
        buffer = " | " * (len(self._block_depths) - 1)
        logger.debug(buffer + "%s(%s)" % (name, ", ".join(str(i) for i in local_vars)))
        if isinstance(f, HostFunc):  # Call native function
            self._publish("will_call_hostfunc", f, local_vars)
            res = list(f.hostcode(self._state, *local_vars))
            self._publish("did_call_hostfunc", f, local_vars, res)
            logger.info("HostFunc returned: %s", res)
            assert len(res) == len(ty.result_types)
            for r, t in zip(res, ty.result_types):
                assert t in {I32, I64, F32, F64}
                # Even though I32, I64, F32, and F64 all have `cast` class methods, mypy can't figure out that
                # t has to be one of those since it doesn't evaluate the previous assert. Note that `isinstance`
                # won't work here since we're using the actual types, not instances of them.
                stack.push(t.cast(r))  # type: ignore
        else:  # Call WASM function
            assert isinstance(f, FuncInst), "Got a non-WASM function! (Maybe cast to HostFunc?)"
            for cast in f.code.locals:
                local_vars.append(cast(0))
            frame = Frame(local_vars, f.module)
            stack.push(
                Activation(
                    len(ty.result_types), frame, expected_block_depth=len(self._block_depths)
                )  # When we pop this frame, we expect to be expected_block_depth call frames deep
            )
            self._block_depths.append(0)  # We're entering a new function call context
            self.block(store, stack, ty.result_types, f.code.body)

    def exec_expression(self, store: Store, stack: "Stack", expr: WASMExpression):
        """
        Pushes the given expression to the stack, calls exec_instruction until there are no more instructions to exec,
        then returns the top value on the stack. Used during initialization to calculate global values, memory offsets,
        element offsets, etc.

        :param expr: The expression to execute
        :return: The result of the expression
        """
        self.push_instructions(expr)
        self._publish("will_exec_expression", expr)
        while self.exec_instruction(store, stack):
            pass
        self._publish("did_exec_expression", expr, stack.peek())
        return stack.pop()

    def enter_block(self, insts, label: "Label", stack: "Stack"):
        """
        Push the instructions for the next block to the queue and bump the block depth number

        https://www.w3.org/TR/wasm-core-1/#exec-instr-seq-enter

        :param insts: Instructions for this block
        :param label: Label referencing the continuation of this block
        :param stack: The execution stack (where we push the label)
        """
        stack.push(label)
        self._block_depths[-1] += 1
        self.push_instructions(insts)

    def exit_block(self, stack: "Stack"):
        """
        Cleans up after execution of a code block.

        https://www.w3.org/TR/wasm-core-1/#exiting--hrefsyntax-instrmathitinstrast-with-label--l
        """
        # Look for a label on the stack
        label_idx = stack.find_type(Label)
        if label_idx is not None:
            logger.debug(
                "EXITING BLOCK (FD: %d, BD: %d)", len(self._block_depths), self._block_depths[-1]
            )
            # Pop the values above the label
            vals = []
            while not isinstance(stack.peek(), Label):
                vals.append(stack.pop())
                assert isinstance(vals[-1], Value_t), f"{type(vals[-1])} is not a value or a label"
            label = stack.pop()
            assert isinstance(label, Label), f"Stack contained a {type(label)} instead of a Label"
            # Decrement the block number
            self._block_depths[-1] -= 1
            # Put the values back on the stack and discard the label
            for v in vals[::-1]:
                stack.push(v)

    def exit_function(self, stack: "AtomicStack"):
        """
        Discards the current frame, allowing execution to return to the point after the call

        https://www.w3.org/TR/wasm-core-1/#returning-from-a-function%E2%91%A0
        """
        if len(self._block_depths) > 1:  # Only if we're in a _real_ function, not initialization
            # Pop return values
            f = stack.get_frame()
            n = f.arity
            stack.has_type_on_top(Value_t, n)
            vals = [stack.pop() for _ in range(n)]
            logger.debug(
                "EXITING FUNCTION (FD: %d, BD: %d) (%s)",
                len(self._block_depths),
                self._block_depths[-1],
                vals,
            )
            assert isinstance(
                stack.peek(), Activation
            ), f"Stack should have an activation on top, instead has {type(stack.peek())}"

            # Discard call frame
            self._block_depths.pop()
            stack.pop()

            # Replace return values
            for v in vals[::-1]:
                stack.push(v)

    def push_instructions(self, insts: WASMExpression):
        """
        Pushes instructions into the instruction queue.
        :param insts: Instructions to push
        """
        for i in insts[::-1]:
            self._instruction_queue.appendleft(i)

    def look_forward(self, *opcodes) -> typing.List[Instruction]:
        """
        Pops contents of the instruction queue until it finds an instruction with an opcode in the argument *opcodes.
        Used to find the end of a code block in the flat instruction queue. For this reason, it calls itself
        recursively (looking for the `end` instruction) if it encounters a `block`, `loop`, or `if` instruction.

        :param opcodes: Tuple of instruction opcodes to look for
        :return: The list of instructions popped before encountering the target instruction.
        """
        out = []
        i = self._instruction_queue.popleft()
        while i.opcode not in opcodes:
            out.append(i)

            # Call recursively if we encounter another block
            if i.opcode in {0x02, 0x03, 0x04}:
                out += self.look_forward(0x0B)

            if len(self._instruction_queue) == 0:
                raise RuntimeError(
                    "Couldn't find an instruction with opcode "
                    + ", ".join(hex(op) for op in opcodes)
                )
            i = self._instruction_queue.popleft()
        out.append(i)
        return out

    def exec_instruction(
        self,
        store: Store,
        stack: "Stack",
        advice: typing.Optional[typing.List[bool]] = None,
        current_state=None,
    ) -> bool:
        """
        The core instruction execution function. Pops an instruction from the queue, then dispatches it to the Executor
        if it's a numeric instruction, or executes it internally if it's a control-flow instruction.

        :param store: The execution Store to use, passed in from the parent WASMWorld. This is passed to almost all
        | instruction implementations, but for brevity's sake, it's only explicitly documented here.
        :param stack: The execution Stack to use, likewise passed in from the parent WASMWorld and only documented here,
        | despite being passed to all the instruction implementations.
        :param advice: A list of concretized conditions to advice execution of the instruction.
        :return: True if execution succeeded, False if there are no more instructions to execute
        """
        # Maps return types from instruction immediates into actual types
        ret_type_map = {-1: [I32], -2: [I64], -3: [F32], -4: [F64], -64: []}
        self._advice = advice
        self._state = current_state
        # Use the AtomicStack context manager to catch Concretization and roll back changes
        with AtomicStack(stack) as aStack:
            # print("Instructions:", self._instruction_queue)
            if self._instruction_queue:
                try:
                    inst = self._instruction_queue.popleft()
                    logger.info(
                        "%s: %s (%s)",
                        hex(inst.opcode),
                        inst.mnemonic,
                        debug(inst.imm) if inst.imm else "",
                    )
                    self._publish("will_execute_instruction", inst)
                    if 0x2 <= inst.opcode <= 0x11:  # This is a control-flow instruction
                        self.executor.zero_div = _eval_maybe_symbolic(
                            self._state, self.executor.zero_div
                        )
                        if self.executor.zero_div:
                            raise ZeroDivisionTrap()
                        self.executor.overflow = _eval_maybe_symbolic(
                            self._state, self.executor.overflow
                        )
                        if self.executor.overflow:
                            raise OverflowDivisionTrap()

                        if inst.opcode == 0x02:
                            self.block(
                                store,
                                aStack,
                                # Get return type from the immediate. Unfortunately, since mypy doesn't know the
                                # immediate type, it doesn't like this and we have to ignore the type
                                ret_type_map[inst.imm.sig],  # type: ignore
                                self.look_forward(0x0B),  # Get the contents of this block
                            )
                        elif inst.opcode == 0x03:
                            self.loop(store, aStack, inst)
                        elif inst.opcode == 0x04:
                            # Get the appropriate return type based on the immediate. Same issue w/ immediate types
                            self.if_(store, aStack, ret_type_map[inst.imm.sig])  # type: ignore
                        elif inst.opcode == 0x05:
                            self.else_(store, aStack)
                        elif inst.opcode == 0x0B:
                            self.end(store, aStack)
                        elif inst.opcode == 0x0C:
                            # Extract the relative depth from the immediate because it makes br's interface
                            # a little bit cleaner. Same issue w/ mypy not understanding immediate types
                            self.br(store, aStack, inst.imm.relative_depth)  # type: ignore
                        elif inst.opcode == 0x0D:
                            assert isinstance(inst.imm, BranchImm)
                            self.br_if(store, aStack, inst.imm)
                        elif inst.opcode == 0x0E:
                            assert isinstance(inst.imm, BranchTableImm)
                            self.br_table(store, aStack, inst.imm)
                        elif inst.opcode == 0x0F:
                            self.return_(store, aStack)
                        elif inst.opcode == 0x10:
                            assert isinstance(inst.imm, CallImm)
                            self.call(store, aStack, inst.imm)
                        elif inst.opcode == 0x11:
                            assert isinstance(inst.imm, CallIndirectImm)
                            self.call_indirect(store, aStack, inst.imm)
                        else:
                            raise Exception("Unhandled control flow instruction")
                    else:  # This is a numeric instruction, hand it to the Executor
                        self.executor.dispatch(inst, store, aStack)
                    self._publish("did_execute_instruction", inst)
                    return True
                except Concretize as exc:
                    # Push the last instruction back to the queue so it will be reattempted after concretization
                    self._instruction_queue.appendleft(inst)
                    raise exc
                except Trap as exc:
                    # Treat traps as an exit from the current call frame. This is something of a kludge to make
                    # the tests pass. I may need to revisit this in the future because I haven't thoroughly explored
                    # or thought about what the correct behavior is here.
                    self._block_depths.pop()
                    logger.info("Trap: %s", str(exc))
                    self._publish("will_raise_trap", exc)
                    raise exc

            elif aStack.find_type(Label):
                # This used to raise a runtime error, but since we have some capacity to recover after a trap, we
                # demote it to a logger.info
                logger.info(
                    "The instruction queue is empty, but there are still labels on the stack. This should only happen when re-executing after a Trap"
                )
        return False

    def get_export(
        self, name: str, store: Store
    ) -> typing.Union[ProtoFuncInst, TableInst, MemInst, GlobalInst, typing.Callable]:
        """
        Retrieves a value exported by this module instance from store

        :param name: The name of the exported value to get
        :param store: The current execution store (where the export values live)
        :return: The value of the export
        """
        export_addr = self.get_export_address(name)
        if isinstance(export_addr, FuncAddr):
            return store.funcs[export_addr]
        if isinstance(export_addr, TableAddr):
            return store.tables[export_addr]
        if isinstance(export_addr, MemAddr):
            return store.mems[export_addr]
        if isinstance(export_addr, GlobalAddr):
            return store.globals[export_addr]
        raise RuntimeError("Unkown export type: " + str(type(export_addr)))

    def get_export_address(
        self, name: str
    ) -> typing.Union[FuncAddr, TableAddr, MemAddr, GlobalAddr]:
        """
        Retrieves the address of a value exported by this module within the store

        :param name: The name of the exported value to get
        :return: The address of the desired export
        """
        if name not in self.export_map:
            raise MissingExportException(name)
        export: ExportInst = self.exports[self.export_map[name]]
        assert export.name == name, f"Export name mismatch (expected {name}, got {export.name})"
        return export.value

    def block(
        self, store: "Store", stack: "Stack", ret_type: typing.List[ValType], insts: WASMExpression
    ):
        """
        Execute a block of instructions. Creates a label with an empty continuation and the proper arity, then enters
        the block of instructions with that label.

        https://www.w3.org/TR/wasm-core-1/#exec-block

        :param ret_type: List of expected return types for this block. Really only need the arity
        :param insts: Instructions to execute
        """
        arity = len(ret_type)
        label = Label(arity, [])
        self.enter_block(insts, label, stack)

    def loop(self, store: "Store", stack: "AtomicStack", loop_inst):
        """
        Enter a loop block. Creates a label with a copy of the loop as a continuation, then enters the loop instructions
        with that label.

        https://www.w3.org/TR/wasm-core-1/#exec-loop

        :param loop_inst: The current insrtuction
        """
        # Grab the instructions that make up the loop
        insts = self.look_forward(0x0B)
        # Create a label with the full loop
        label = Label(0, [loop_inst] + insts)
        # Enter the rest of the block
        self.enter_block(insts, label, stack)

    def extract_block(self, partial_list: typing.Deque[Instruction]) -> typing.Deque[Instruction]:
        """
        Recursively extracts blocks from a list of instructions, similar to self.look_forward. The primary difference
        is that this version takes a list of instructions to operate over, instead of popping instructions from the
        instruction queue.

        :param partial_list: List of instructions to extract the block from
        :return: The extracted block
        """
        out: typing.Deque[Instruction] = deque()
        i = partial_list.popleft()
        while i.opcode != 0x0B:
            out.append(i)
            if i.opcode in {0x02, 0x03, 0x04}:
                out += self.extract_block(partial_list)
            if len(partial_list) == 0:
                raise RuntimeError("Couldn't find an end to this block!")
            i = partial_list.popleft()
        out.append(i)
        return out

    def _split_if_block(
        self, partial_list: typing.Deque[Instruction]
    ) -> typing.Tuple[typing.Deque[Instruction], typing.Deque[Instruction]]:
        """
        Splits an if block into its true and false portions. Handles nested blocks in both the true and false branches,
        and when one branch is empty and/or the else instruction is missing.

        :param partial_list: Complete if block that needs to be split
        :return: The true block and the false block
        """
        t_block: typing.Deque[Instruction] = deque()
        assert partial_list[-1].opcode == 0x0B, "This block is missing an end instruction!"
        i = partial_list.popleft()
        while i.opcode not in {0x05, 0x0B}:
            t_block.append(i)
            if i.opcode in {0x02, 0x03, 0x04}:
                t_block += self.extract_block(partial_list)
            if len(partial_list) == 0:
                raise RuntimeError("Couldn't find an end to this if statement!")
            i = partial_list.popleft()
        t_block.append(i)

        return t_block, partial_list

    def if_(self, store: "Store", stack: "AtomicStack", ret_type: typing.List[type]):
        """
        Brackets two nested sequences of instructions. If the value on top of the stack is nonzero, enter the first
        block. If not, enter the second.

        https://www.w3.org/TR/wasm-core-1/#exec-if
        """
        stack.has_type_on_top(I32, 1)
        i = stack.pop()
        if self._advice is not None:
            cond = self._advice[0]
        elif isinstance(i, Expression):
            raise ConcretizeCondition("Concretizing if_", i != 0, self._advice)
        else:
            cond = i != 0

        insn_block = self.look_forward(0x0B)  # Get the entire `if` block
        # Split it into the true and false branches
        t_block, f_block = self._split_if_block(deque(insn_block))
        label = Label(len(ret_type), [])

        # Enter the true branch if the top of the stack is nonzero
        if cond:
            self.enter_block(list(t_block), label, stack)
        # Otherwise, take the false branch
        else:
            # Handle if there wasn't an `else` instruction
            if len(f_block) == 0:
                assert t_block[-1].opcode == 0x0B  # The true block is just an `end`
                f_block.append(t_block[-1])
            self.enter_block(list(f_block), label, stack)

    def else_(self, store: "Store", stack: "AtomicStack"):
        """
        Marks the end of the first block of an if statement.
        Typically, `if` blocks look like: `if <instructions> else <instructions> end`. That's not always the case. See:
        https://webassembly.github.io/spec/core/text/instructions.html#abbreviations
        """
        self.exit_block(stack)

    def end(self, store: "Store", stack: "AtomicStack"):
        """
        Marks the end of an instruction block or function
        """
        if self._block_depths[-1] > 0:
            # We're at the end of a block, but haven't finished the function
            self.exit_block(stack)
        if self._block_depths[-1] == 0:
            # We've finished all the blocks in the function
            self.exit_function(stack)

    def br(self, store: "Store", stack: "AtomicStack", label_depth: int):
        """
        Branch to the `label_depth`th label deep on the stack

        https://www.w3.org/TR/wasm-core-1/#exec-br
        """
        assert stack.has_at_least(Label, label_depth + 1)

        label: Label = stack.get_nth(Label, label_depth)
        stack.has_type_on_top(Value_t, label.arity)
        vals = [stack.pop() for _ in range(label.arity)]

        # Pop the higher labels and values from the stack and discard them
        for _ in range(label_depth + 1):
            while isinstance(stack.peek(), Value_t):
                stack.pop()
            assert isinstance(stack.peek(), Label)
            stack.pop()
            assert self._block_depths[-1] > 0, "Trying to break out of a function call"
            self._block_depths[-1] -= 1

        # Push the values expected by this branch back onto the stack
        for v in vals[::-1]:
            stack.push(v)

        # Purge the next label_depth blocks of instructions from the queue until we've reached the appropriate depth
        for _ in range(label_depth + 1):
            self.look_forward(0x0B, 0x05)
        # Push the instructions from the label
        self.push_instructions(label.instr)

    def br_if(self, store: "Store", stack: "AtomicStack", imm: BranchImm):
        """
        Perform a branch if the value on top of the stack is nonzero

        https://www.w3.org/TR/wasm-core-1/#exec-br-if
        """
        stack.has_type_on_top(I32, 1)
        i = stack.pop()
        if self._advice is not None:
            cond = self._advice[0]
        elif isinstance(i, Expression):
            raise ConcretizeCondition("Concretizing br_if_", i != 0, self._advice)
        else:
            cond = i != 0

        if cond:
            self.br(store, stack, imm.relative_depth)

    def br_table(self, store: "Store", stack: "AtomicStack", imm: BranchTableImm):
        """
        Branch to the nth label deep on the stack where n is found by looking up a value in a table given by the
        immediate, indexed by the value on top of the stack.

        https://www.w3.org/TR/wasm-core-1/#exec-br-table
        """
        stack.has_type_on_top(I32, 1)
        i = stack.pop()
        if self._advice is not None:
            in_range = self._advice[0]
            if not in_range:
                i = I32.cast(imm.target_count)
            elif issymbolic(i):
                raise ConcretizeStack(-1, I32, "Concretizing br_table index", i)
        elif isinstance(i, Expression):
            raise ConcretizeCondition(
                "Concretizing br_table range check",
                Operators.AND((i >= 0), (i < imm.target_count)),
                self._advice,
            )

        # The spec (https://www.w3.org/TR/wasm-core-1/#exec-br-table) says that if i < the length of the table,
        # execute br target_table[i]. The tests, however, pass a negative i, which doesn't make sense in this
        # situation. For that reason, we use `in range` even though it's a different behavior.
        if i in range(imm.target_count):
            assert isinstance(i, int)  # If we made it past the concretization, i should be an I32
            lab = imm.target_table[i]
        else:
            lab = imm.default_target
        self.br(store, stack, lab)

    def return_(self, store: "Store", stack: "AtomicStack"):
        """
        Return from the function (ie branch to the outermost block)

        https://www.w3.org/TR/wasm-core-1/#exec-return
        """
        # Pop everything from the stack until we get to the current call frame, then push back the topmost
        # n values, where n is the number of expected returns for the current function
        f = stack.get_frame()
        n = f.arity
        stack.has_type_on_top(Value_t, n)
        ret = [stack.pop() for _i in range(n)]
        while not isinstance(stack.peek(), (Activation, Frame)):
            stack.pop()
        assert stack.peek() == f
        stack.pop()
        for r in ret[::-1]:
            stack.push(r)

        # Ensure that we've returned to the correct block depth for the frame we just popped
        while len(self._block_depths) > f.expected_block_depth:
            # Discard the rest of the current block, then keep discarding blocks from the instruction queue
            # until we've purged the rest of this function.
            for i in range(self._block_depths[-1]):
                self.look_forward(0x0B, 0x05)
            # Pop the current function call from the block depth tracker
            self._block_depths.pop()

    def call(self, store: "Store", stack: "AtomicStack", imm: CallImm):
        """
        Invoke the function at the address in the store given by the immediate.

        https://www.w3.org/TR/wasm-core-1/#exec-call
        """
        f = stack.get_frame()
        assert imm.function_index in range(len(f.frame.module.funcaddrs))
        a = f.frame.module.funcaddrs[imm.function_index]
        self._invoke_inner(stack, a, store)

    def call_indirect(self, store: "Store", stack: "AtomicStack", imm: CallIndirectImm):
        """
        A function call, but with extra steps. Specifically, you find the index of the function to call by looking in
        the table at the index given by the immediate.

        https://www.w3.org/TR/wasm-core-1/#exec-call-indirect
        """
        f = stack.get_frame()
        assert f.frame.module.tableaddrs
        ta = f.frame.module.tableaddrs[0]
        assert ta in range(len(store.tables))
        tab = store.tables[ta]
        assert imm.type_index in range(len(f.frame.module.types))
        ft_expect = f.frame.module.types[imm.type_index]

        stack.has_type_on_top(I32, 1)
        item = stack.pop()
        if self._advice is not None:
            in_range = self._advice[0]
            if not in_range:
                i = I32.cast(len(tab.elem))
            elif issymbolic(item):
                raise ConcretizeStack(-1, I32, "Concretizing call_indirect operand", item)
            else:
                i = item
        elif isinstance(item, Expression):
            raise ConcretizeCondition(
                "Concretizing call_indirect range check",
                (item >= 0) & (item < len(tab.elem)),
                self._advice,
            )
        else:
            i = item
            assert isinstance(i, I32)

        if i not in range(len(tab.elem)):
            raise NonExistentFunctionCallTrap()
        if tab.elem[i] is None:
            raise NonExistentFunctionCallTrap()
        a = tab.elem[i]
        assert a is not None
        assert a in range(len(store.funcs))
        func = store.funcs[a]
        ft_actual = func.type
        if ft_actual != ft_expect:
            raise TypeMismatchTrap(ft_actual, ft_expect)
        self._invoke_inner(stack, a, store)


@dataclass
class Label:
    """
    A branch label that can be pushed onto the stack and then jumped to

    https://www.w3.org/TR/wasm-core-1/#labels%E2%91%A0
    """

    arity: int  #: the number of values this branch expects to read from the stack
    instr: typing.List[
        Instruction
    ]  #: The sequence of instructions to execute if we branch to this label


@dataclass
class Frame:
    """
    Holds more call data, nested inside an activation (for reasons I don't understand)

    https://www.w3.org/TR/wasm-core-1/#activations-and-frames%E2%91%A0
    """

    locals: typing.List[Value]  #: The values of the local variables for this function call
    module: ModuleInstance  #: A reference to the parent module instance in which the function call was made


@dataclass
class Activation:
    """
    Pushed onto the stack with each function invocation to keep track of the call stack

    https://www.w3.org/TR/wasm-core-1/#activations-and-frames%E2%91%A0
    """

    arity: int  #: The expected number of return values from the function call associated with the underlying frame
    frame: Frame  #: The nested frame
    expected_block_depth: int  #: Internal helper used to track the expected block depth when we exit this label

    def __init__(self, arity, frame, expected_block_depth=0):
        self.arity = arity
        self.frame = frame
        self.expected_block_depth = expected_block_depth


StackItem = typing.Union[Value, Label, Activation]


class Stack(Eventful):
    """
    Stores the execution stack & provides helper methods

    https://www.w3.org/TR/wasm-core-1/#stack%E2%91%A0
    """

    data: typing.Deque[StackItem]  #: Underlying datastore for the "stack"

    _published_events = {"push_item", "pop_item"}

    def __init__(self, init_data=None):
        """
        :param init_data: Optional initialization value
        """
        self.data = init_data if init_data else deque()
        super().__init__()

    def __getstate__(self):
        state = super().__getstate__()
        state["data"] = self.data
        return state

    def __setstate__(self, state):
        self.data = state["data"]
        super().__setstate__(state)

    def push(self, val: StackItem) -> None:
        """
        Push a value to the stack

        :param val: The value to push
        :return: None
        """
        if isinstance(val, list):
            raise RuntimeError("Don't push lists")
        logger.debug("+%d %s (%s)", len(self.data), val, type(val))
        self._publish("will_push_item", val, len(self.data))
        self.data.append(val)
        self._publish("did_push_item", val, len(self.data))

    def pop(self) -> StackItem:
        """
        Pop a value from the stack

        :return: the popped value
        """
        logger.debug("-%d %s (%s)", len(self.data) - 1, self.peek(), type(self.peek()))
        self._publish("will_pop_item", len(self.data))
        item = self.data.pop()
        self._publish("did_pop_item", item, len(self.data))
        return item

    def peek(self) -> typing.Optional[StackItem]:
        """
        :return: the item on top of the stack (without removing it)
        """
        if self.data:
            return self.data[-1]
        return None

    def empty(self) -> bool:
        """
        :return: True if the stack is empty, otherwise False
        """
        return len(self.data) == 0

    def has_type_on_top(self, t: typing.Union[type, typing.Tuple[type, ...]], n: int):
        """
        *Asserts* that the stack has at least n values of type t or type BitVec on the top

        :param t: type of value to look for (Bitvec is always included as an option)
        :param n: Number of values to check
        :return: True
        """
        for i in range(1, n + 1):
            assert isinstance(
                self.data[i * -1], (t, BitVec)
            ), f"{type(self.data[i * -1])} is not an {t}!"
        return True

    def find_type(self, t: type) -> typing.Optional[int]:
        """
        :param t: The type to look for
        :return: The depth of the first value of type t
        """
        for idx, v in enumerate(reversed(self.data)):
            if isinstance(v, t):
                return -1 * idx
        return None

    def has_at_least(self, t: type, n: int) -> bool:
        """
        :param t: type to look for
        :param n: number to look for
        :return: whether the stack contains at least n values of type t
        """
        count = 0
        for v in reversed(self.data):
            if isinstance(v, t):
                count += 1
            if count == n:
                return True
        return False

    def get_nth(self, t: type, n: int) -> typing.Optional[StackItem]:
        """
        :param t: type to look for
        :param n: number to look for
        :return: the nth item of type t from the top of the stack, or None
        """
        seen = 0
        for v in reversed(self.data):
            if isinstance(v, t):
                if seen == n:
                    return v
                seen += 1
        return None

    def get_frame(self) -> Activation:
        """
        :return: the topmost frame (Activation) on the stack
        """
        for item in reversed(self.data):
            if isinstance(item, Activation):
                return item
        raise RuntimeError("Couldn't find a frame on the stack")


class AtomicStack(Stack):  # lgtm [py/missing-call-to-init]
    """
    Allows for the rolling-back of the stack in the event of a concretization exception.
    Inherits from Stack so that the types will be correct, but never calls `super`.
    Provides a context manager that will intercept Concretization Exceptions before raising them.
    """

    class PushItem:
        pass

    @dataclass
    class PopItem:
        val: StackItem

    def __init__(self, parent: Stack):
        self.parent = parent
        self.actions: typing.List[typing.Union[AtomicStack.PushItem, AtomicStack.PopItem]] = []

    def __getstate__(self):
        state = {"parent": self.parent, "actions": self.actions}
        return state

    def __setstate__(self, state):
        self.parent = state["parent"]
        self.actions = state["actions"]

    def __enter__(self):
        return self

    def __exit__(self, exc_type, exc_val, exc_tb):
        if isinstance(exc_val, Concretize):
            logger.info("Rolling back stack for concretization")
            self.rollback()

    def rollback(self):
        while self.actions:
            action = self.actions.pop()
            if isinstance(action, AtomicStack.PopItem):
                self.parent.push(action.val)
            elif isinstance(action, AtomicStack.PushItem):
                self.parent.pop()

    def push(self, val: StackItem) -> None:
        self.actions.append(AtomicStack.PushItem())
        self.parent.push(val)

    def pop(self) -> StackItem:
        val = self.parent.pop()
        self.actions.append(AtomicStack.PopItem(val))
        return val

    def peek(self):
        return self.parent.peek()

    def empty(self):
        return self.parent.empty()

    def has_type_on_top(self, t: typing.Union[type, typing.Tuple[type, ...]], n: int):
        return self.parent.has_type_on_top(t, n)

    def find_type(self, t: type):
        return self.parent.find_type(t)

    def has_at_least(self, t: type, n: int):
        return self.parent.has_at_least(t, n)

    def get_nth(self, t: type, n: int):
        return self.parent.get_nth(t, n)

    def get_frame(self) -> Activation:
        return self.parent.get_frame()


@dataclass
class FuncInst(ProtoFuncInst):
    """
    Instance type for WASM functions
    """

    module: ModuleInstance
    code: "Function"


@dataclass
class HostFunc(ProtoFuncInst):
    """
    Instance type for native functions that have been provided via import
    """

    hostcode: types.FunctionType  #: the native function. Should accept ConstraintSet as the first argument

    def allocate(
        self, store: Store, functype: FunctionType, host_func: types.FunctionType
    ) -> FuncAddr:
        """
        Currently not needed.

        https://www.w3.org/TR/wasm-core-1/#host-functions%E2%91%A2
        """
        pass


class ConcretizeCondition(Concretize):
    """Tells Manticore to concretize a condition required to direct execution."""

    def __init__(
        self,
        message: str,
        condition: Bool,
        current_advice: typing.Optional[typing.List[bool]],
        **kwargs,
    ):
        """
        :param message: Debug message describing the reason for concretization
        :param condition: The boolean expression to concretize
        """

        advice = current_advice if current_advice is not None else []

        def setstate(state, value: bool):
            state.platform.advice = advice + [value]

        super().__init__(message, condition, setstate, **kwargs)
