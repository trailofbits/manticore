import typing
from dataclasses import dataclass
from .types import (
    TypeIdx,
    TableIdx,
    FuncIdx,
    GlobalIdx,
    MemIdx,
    Byte,
    ValType,
    FunctionType,
    TableType,
    MemoryType,
    GlobalType,
    LimitType,
    Name,
    WASMExpression,
    convert_instructions,
    I32,
    I64,
    F32,
    F64,
)
from .runtime_structure import (
    Store,
    ModuleInstance,
    FuncAddr,
    TableAddr,
    MemAddr,
    GlobalAddr,
    FuncInst,
    TableInst,
    MemInst,
    GlobalInst,
    Value,
)
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
)

ExportDesc: type = typing.Union[FuncIdx, TableIdx, MemIdx, GlobalIdx]
ImportDesc: type = typing.Union[TypeIdx, TableType, MemoryType, GlobalType]


@dataclass
class Function:
    """
    A WASM Function

    https://www.w3.org/TR/wasm-core-1/#functions%E2%91%A0
    """

    type: TypeIdx  #: The index of a type defined in the module that corresponds to this function's type signature
    locals: typing.List[ValType]  #: Vector of mutable local variables (and their types)
    body: WASMExpression  #: Sequence of WASM instructions, should leave the appropriate type on the stack

    def allocate(self, store: Store, module: ModuleInstance) -> FuncAddr:
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

    def allocate(self, store: Store) -> TableAddr:
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

    def allocate(self, store: Store) -> MemAddr:
        """
        https://www.w3.org/TR/wasm-core-1/#memories%E2%91%A5

        :param store: Destination Store that we'll insert this Memory into after allocation
        :return: The address of this within `store`
        """
        a = MemAddr(len(store.mems))
        store.mems.append(
            MemInst(
                [
                    0x0
                    for _i in range(
                        self.type.min * (64 * 1024)
                    )  # https://www.w3.org/TR/wasm-core-1/#page-size
                ],  # TODO - these should be symbolic, right?
                self.type.max,
            )
        )
        return a


@dataclass
class Global:
    """
    A global variable of a given type

    https://www.w3.org/TR/wasm-core-1/#globals%E2%91%A0
    """

    type: GlobalType  #: The type of the variable
    init: WASMExpression  #: A (constant) sequence of WASM instructions that calculates the value for the global

    def allocate(self, store: Store, val: Value) -> GlobalAddr:
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
    init: typing.List[Byte]  #: List of bytes to copy into the memory


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


def strip_quotes(rough_name: str) -> str:
    """
    For some reason, the parser returns the function names with quotes around them

    :param rough_name:
    :return:
    """
    return rough_name[1:-1]


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
        self._raw = state["_raw"]

    @classmethod
    def load(cls, filename: str):
        """
        Converts a WASM module in binary format into Python types that Manticore can understand

        :param filename: name of the WASM module
        :return: Module
        """
        type_map = [
            F64,
            F32,
            I64,
            I32,
        ]  # Data types are negatively indexed, which is why I32 is last

        m: Module = cls()
        with open(filename, "rb") as wasm_file:
            m._raw = wasm_file.read()

        module_iter = decode_module(m._raw)
        _header = next(module_iter)
        section: Section
        # Parse the sections from the WASM module into internal types. For each section, the code usually resembles:
        # `module.<something>.append(<InstanceOfSomething>(data, from, binary, module))`
        for section, section_data in module_iter:
            sec_id = section_data.id
            if sec_id == SEC_TYPE:  # https://www.w3.org/TR/wasm-core-1/#type-section%E2%91%A0
                for ft in section_data.payload.entries:
                    m.types.append(
                        FunctionType(
                            ft.param_types,
                            [type_map[ft.return_type] for _i in range(ft.return_count)],
                        )
                    )
            elif sec_id == SEC_IMPORT:  # https://www.w3.org/TR/wasm-core-1/#import-section%E2%91%A0
                for i in section_data.payload.entries:
                    ty_map = i.get_decoder_meta()["types"]
                    if i.kind == 0:
                        desc = TypeIdx(i.type.type)
                    elif i.kind == 1:
                        desc = TableType(
                            LimitType(i.type.limits.initial, i.type.limits.maximum),
                            type_map[i.type.element_type],
                        )
                    elif i.kind == 2:
                        desc = MemoryType(i.type.limits.initial, i.type.limits.maximum)
                    elif i.kind == 3:
                        desc = GlobalType(bool(i.type.mutability), type_map[i.type.content_type])
                    else:
                        raise RuntimeError("Can't decode kind field of:", i.kind)
                    m.imports.append(
                        Import(
                            ty_map["module_str"].to_string(i.module_str),
                            strip_quotes(ty_map["field_str"].to_string(i.field_str)),
                            desc,
                        )
                    )
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
            # TODO - custom sections (https://www.w3.org/TR/wasm-core-1/#custom-section%E2%91%A0)

        return m
