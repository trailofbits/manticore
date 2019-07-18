import typing
from dataclasses import dataclass
from .types import U32, Byte, ValType, FunctionType, TableType, MemoryType, GlobalType, LimitType
from wasm import decode_module, Section, Opcode
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


class Indices:
    typeidx: type = U32
    funcidx: type = U32
    tableidx: type = U32
    memidx: type = U32
    globalidx: type = U32
    localidx: type = U32
    labelidx: type = U32


Expression = typing.Sequence[Opcode]
ExportDesc = typing.Union[Indices.funcidx, Indices.tableidx, Indices.memidx, Indices.globalidx]
ImportDesc = typing.Union[Indices.typeidx, TableType, MemoryType, GlobalType]
Name: type = str


@dataclass
class Function:
    type: Indices.typeidx
    locals: typing.List[ValType]
    body: Expression


@dataclass
class Table:
    type: TableType


@dataclass
class Memory:
    type: MemoryType


@dataclass
class Global:
    type: GlobalType
    init: Expression


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
                pass
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
                mapping = [Indices.funcidx, Indices.tableidx, Indices.memidx, Indices.globalidx]
                for e in section_data.payload.entries:
                    m.exports.append(
                        Export(e.field_str, mapping[e.kind](e.index))
                    )  # TODO - Is this the right way to create an ExportDesc?
            elif sec_id == SEC_START:
                pass
            elif sec_id == SEC_ELEMENT:
                pass
            elif sec_id == SEC_CODE:
                for idx, c in enumerate(
                    section_data.payload.bodies
                ):  # TODO - Is the index guaranteed to match here?
                    m.funcs[idx].locals = c.locals
                    m.funcs[idx].body = c.code
            elif sec_id == SEC_DATA:
                pass

        return m
