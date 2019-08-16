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

ExportDesc = typing.Union[FuncIdx, TableIdx, MemIdx, GlobalIdx]
ImportDesc = typing.Union[TypeIdx, TableType, MemoryType, GlobalType]


@dataclass
class Function:
    type: TypeIdx
    locals: typing.List[ValType]
    body: WASMExpression

    def allocate(self, store: Store, module: ModuleInstance) -> FuncAddr:
        a = FuncAddr(len(store.funcs))
        store.funcs.append(FuncInst(module.types[self.type], module, self))
        return a


@dataclass
class Table:
    type: TableType

    def allocate(self, store: Store, table_type: TableType) -> TableAddr:
        a = TableAddr(len(store.tables))
        store.tables.append(
            TableInst([None for _i in range(table_type.limits.min)], table_type.limits.max)
        )
        return a


@dataclass
class Memory:
    type: MemoryType

    def allocate(self, store: Store, mem_type: MemoryType) -> MemAddr:
        a = MemAddr(len(store.mems))
        store.mems.append(
            MemInst(
                [
                    0x0 for _i in range(mem_type.min * (64 * 1024))
                ],  # TODO - these should be symbolic, right?
                mem_type.max,
            )
        )
        return a


@dataclass
class Global:
    type: GlobalType
    init: WASMExpression

    def allocate(self, store: Store, global_type: GlobalType, val: Value) -> GlobalAddr:
        a = GlobalAddr(len(store.globals))
        store.globals.append(GlobalInst(val, global_type.mut))
        return a


@dataclass
class Elem:
    table: TableIdx
    offset: WASMExpression
    init: typing.List[FuncIdx]


@dataclass
class Data:
    data: MemIdx
    offset: WASMExpression
    init: typing.List[Byte]


@dataclass
class Import:
    module: Name
    name: Name
    desc: ImportDesc


@dataclass
class Export:
    name: Name
    desc: ExportDesc


class Module:
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
        self.start: typing.Optional[FuncIdx] = None
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
        type_map = [F64, F32, I64, I32]

        m = Module()
        with open(filename, "rb") as wasm_file:
            m._raw = wasm_file.read()

        module_iter = decode_module(m._raw)
        _header = next(module_iter)
        section: Section
        for section, section_data in module_iter:
            sec_id = section_data.id
            if sec_id == SEC_TYPE:
                for ft in section_data.payload.entries:
                    m.types.append(
                        FunctionType(
                            ft.param_types,
                            [type_map[ft.return_type] for _i in range(ft.return_count)],
                        )
                    )
            elif sec_id == SEC_IMPORT:
                mapping = (FuncIdx, TableIdx, MemIdx, GlobalIdx)
                for i in section_data.payload.entries:
                    ty_map = i.get_decoder_meta()["types"]
                    m.imports.append(
                        Import(
                            ty_map["module_str"].to_string(i.module_str),
                            eval(
                                ty_map["field_str"].to_string(i.field_str)
                            ),  # TODO - this is also horribly unsafe
                            mapping[i.kind](i.type.type),
                        )
                    )
            elif sec_id == SEC_FUNCTION:
                for f in section_data.payload.types:
                    m.funcs.append(
                        Function(TypeIdx(f), [], [])
                    )  # Get the expressions and locals from the code section
            elif sec_id == SEC_TABLE:
                for t in section_data.payload.entries:
                    m.tables.append(
                        Table(
                            TableType(LimitType(t.limits.initial, t.limits.maximum), FunctionType)
                        )
                    )
            elif sec_id == SEC_MEMORY:
                for mem in section_data.payload.entries:
                    m.mems.append(Memory(LimitType(mem.limits.initial, mem.limits.maximum)))
            elif sec_id == SEC_GLOBAL:
                for g in section_data.payload.globals:
                    m.globals.append(
                        Global(
                            GlobalType(g.type.mutability, type_map[g.type.content_type]),
                            convert_instructions(g.init),
                        )
                    )
            elif sec_id == SEC_EXPORT:
                mapping = (FuncIdx, TableIdx, MemIdx, GlobalIdx)
                for e in section_data.payload.entries:
                    ty = e.get_decoder_meta()["types"]["field_str"]
                    m.exports.append(
                        Export(eval(ty.to_string(e.field_str)), mapping[e.kind](e.index))
                    )  # TODO - This is definitely an unsafe way to strip the quotes
            elif sec_id == SEC_START:
                pass  # TODO - Start func
            elif sec_id == SEC_ELEMENT:
                for e in section_data.payload.entries:
                    m.elem.append(
                        Elem(
                            TableIdx(e.index),
                            convert_instructions(e.offset),
                            [FuncIdx(i) for i in e.elems],
                        )
                    )
            elif sec_id == SEC_CODE:
                for idx, c in enumerate(section_data.payload.bodies):
                    m.funcs[idx].locals = [
                        type_map[e.type] for e in c.locals for _i in range(e.count)
                    ]
                    m.funcs[idx].body = convert_instructions(c.code)
            elif sec_id == SEC_DATA:
                for d in section_data.payload.entries:
                    m.data.append(
                        Data(MemIdx(d.index), convert_instructions(d.offset), d.data.tolist())
                    )  # TODO - the offset and data are probably raw types that we need to process into something
            # TODO - custom sections

        return m
