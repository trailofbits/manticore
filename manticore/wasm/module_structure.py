import typing
from dataclasses import dataclass
from .types import (
    Indices,
    Byte,
    ValType,
    FunctionType,
    TableType,
    MemoryType,
    GlobalType,
    LimitType,
    Name,
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
from wasm.decode import Instruction
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

Expression = typing.Sequence[Instruction]
ExportDesc = typing.Union[Indices.funcidx, Indices.tableidx, Indices.memidx, Indices.globalidx]
ImportDesc = typing.Union[Indices.typeidx, TableType, MemoryType, GlobalType]


@dataclass
class Function:
    type: Indices.typeidx
    locals: typing.List[ValType]
    body: Expression

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
                    0x0 for _i in range(mem_type.min - (64 * 1024))
                ],  # TODO - these should be symbolic, right?
                mem_type.max,
            )
        )
        return a


@dataclass
class Global:
    type: GlobalType
    init: Expression

    def allocate(self, store: Store, global_type: GlobalType, val: Value) -> GlobalAddr:
        a = GlobalAddr(len(store.globals))
        store.append(GlobalInst(val, global_type.mut))
        return a


@dataclass
class Elem:
    table: Indices.tableidx
    offset: Expression
    init: typing.List[Indices.tableidx]


@dataclass
class Data:
    data: Indices.memidx
    offset: Expression
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
        self.start: typing.Optional[Indices.funcidx] = None
        self.imports: typing.List[Import] = []
        self.exports: typing.List[Export] = []

    @classmethod
    def load(cls, filename: str):

        m = Module()
        with open(filename, "rb") as wasm_file:
            m._raw = wasm_file.read()

        module_iter = decode_module(m._raw)
        _header = next(module_iter)
        section: Section
        for section, section_data in module_iter:
            print(section.to_string(section_data))

            sec_id = section_data.id
            if sec_id == SEC_TYPE:
                for ft in section_data.payload.entries:
                    m.types.append(
                        FunctionType(ft.param_types, [ft.return_type])
                    )  # TODO: Decode numeric return types to actual returns
            elif sec_id == SEC_IMPORT:
                mapping = (Indices.funcidx, Indices.tableidx, Indices.memidx, Indices.globalidx)
                for i in section_data.payload.entries:
                    ty_map = i.get_decoder_meta()["types"]
                    m.imports.append(
                        Import(
                            ty_map["module_str"].to_string(i.module_str),
                            ty_map["field_str"].to_string(i.field_str),
                            mapping[i.kind](i.type.type),
                        )
                    )
            elif sec_id == SEC_FUNCTION:
                for f in section_data.payload.types:
                    m.funcs.append(
                        Function(Indices.typeidx(f), [], [])
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
                    pass  # TODO: Create the globals
            elif sec_id == SEC_EXPORT:
                mapping = (Indices.funcidx, Indices.tableidx, Indices.memidx, Indices.globalidx)
                for e in section_data.payload.entries:
                    ty = e.get_decoder_meta()["types"]["field_str"]
                    m.exports.append(
                        Export(eval(ty.to_string(e.field_str)), mapping[e.kind](e.index))
                    )  # TODO - This is definitely unsafe
            elif sec_id == SEC_START:
                pass  # TODO - Start func
            elif sec_id == SEC_ELEMENT:
                pass  # TODO - ELEMENT Section
            elif sec_id == SEC_CODE:
                for idx, c in enumerate(
                    section_data.payload.bodies
                ):  # TODO - Is the index guaranteed to match here?
                    m.funcs[idx].locals = c.locals
                    m.funcs[idx].body = c.code
            elif sec_id == SEC_DATA:
                for d in section_data.payload.entries:
                    m.data.append(
                        Data(Indices.memidx(d.index), d.offset, d.data)
                    )  # TODO - the offset and data are probably raw types
            # TODO - custom sections

        return m
