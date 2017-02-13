#-------------------------------------------------------------------------------
# elftools: dwarf/descriptions.py
#
# Textual descriptions of the various values and enums of DWARF
#
# Eli Bendersky (eliben@gmail.com)
# This code is in the public domain
#-------------------------------------------------------------------------------
from collections import defaultdict

from .constants import *
from .dwarf_expr import GenericExprVisitor
from .die import DIE
from ..common.utils import preserve_stream_pos, dwarf_assert
from ..common.py3compat import bytes2str
from .callframe import instruction_name, CIE, FDE


def set_global_machine_arch(machine_arch):
    global _MACHINE_ARCH
    _MACHINE_ARCH = machine_arch


def describe_attr_value(attr, die, section_offset):
    """ Given an attribute attr, return the textual representation of its
        value, suitable for tools like readelf.

        To cover all cases, this function needs some extra arguments:

        die: the DIE this attribute was extracted from
        section_offset: offset in the stream of the section the DIE belongs to
    """
    descr_func = _ATTR_DESCRIPTION_MAP[attr.form]
    val_description = descr_func(attr, die, section_offset)

    # For some attributes we can display further information
    extra_info_func = _EXTRA_INFO_DESCRIPTION_MAP[attr.name]
    extra_info = extra_info_func(attr, die, section_offset)
    return str(val_description) + '\t' + extra_info


def describe_CFI_instructions(entry):
    """ Given a CFI entry (CIE or FDE), return the textual description of its
        instructions.
    """
    def _assert_FDE_instruction(instr):
        dwarf_assert(
            isinstance(entry, FDE),
            'Unexpected instruction "%s" for a CIE' % instr)

    def _full_reg_name(regnum):
        regname = describe_reg_name(regnum, _MACHINE_ARCH, False)
        if regname:
            return 'r%s (%s)' % (regnum, regname)
        else:
            return 'r%s' % regnum

    if isinstance(entry, CIE):
        cie = entry
    else: # FDE
        cie = entry.cie
        pc = entry['initial_location']

    s = ''
    for instr in entry.instructions:
        name = instruction_name(instr.opcode)

        if name in ('DW_CFA_offset',
                    'DW_CFA_offset_extended', 'DW_CFA_offset_extended_sf',
                    'DW_CFA_val_offset', 'DW_CFA_val_offset_sf'):
            s += '  %s: %s at cfa%+d\n' % (
                name, _full_reg_name(instr.args[0]),
                instr.args[1] * cie['data_alignment_factor'])
        elif name in (  'DW_CFA_restore', 'DW_CFA_restore_extended',
                        'DW_CFA_undefined', 'DW_CFA_same_value',
                        'DW_CFA_def_cfa_register'):
            s += '  %s: %s\n' % (name, _full_reg_name(instr.args[0]))
        elif name == 'DW_CFA_register':
            s += '  %s: %s in %s' % (
                name, _full_reg_name(instr.args[0]),
                _full_reg_name(instr.args[1]))
        elif name == 'DW_CFA_set_loc':
            pc = instr.args[0]
            s += '  %s: %08x\n' % (name, pc)
        elif name in (  'DW_CFA_advance_loc1', 'DW_CFA_advance_loc2',
                        'DW_CFA_advance_loc4', 'DW_CFA_advance_loc'):
            _assert_FDE_instruction(instr)
            factored_offset = instr.args[0] * cie['code_alignment_factor']
            s += '  %s: %s to %016x\n' % (
                name, factored_offset, factored_offset + pc)
            pc += factored_offset
        elif name in (  'DW_CFA_remember_state', 'DW_CFA_restore_state',
                        'DW_CFA_nop'):
            s += '  %s\n' % name
        elif name == 'DW_CFA_def_cfa':
            s += '  %s: %s ofs %s\n' % (
                name, _full_reg_name(instr.args[0]), instr.args[1])
        elif name == 'DW_CFA_def_cfa_sf':
            s += '  %s: %s ofs %s\n' % (
                name, _full_reg_name(instr.args[0]),
                instr.args[1] * cie['data_alignment_factor'])
        elif name == 'DW_CFA_def_cfa_offset':
            s += '  %s: %s\n' % (name, instr.args[0])
        elif name == 'DW_CFA_def_cfa_expression':
            expr_dumper = ExprDumper(entry.structs)
            expr_dumper.process_expr(instr.args[0])
            s += '  %s: (%s)\n' % (name, expr_dumper.get_str())
        elif name == 'DW_CFA_expression':
            expr_dumper = ExprDumper(entry.structs)
            expr_dumper.process_expr(instr.args[1])
            s += '  %s: %s (%s)\n' % (
                name, _full_reg_name(instr.args[0]), expr_dumper.get_str())
        else:
            s += '  %s: <??>\n' % name

    return s


def describe_CFI_register_rule(rule):
    s = _DESCR_CFI_REGISTER_RULE_TYPE[rule.type]
    if rule.type in ('OFFSET', 'VAL_OFFSET'):
        s += '%+d' % rule.arg
    elif rule.type == 'REGISTER':
        s += describe_reg_name(rule.arg)
    return s


def describe_CFI_CFA_rule(rule):
    if rule.expr:
        return 'exp'
    else:
        return '%s%+d' % (describe_reg_name(rule.reg), rule.offset)


def describe_DWARF_expr(expr, structs):
    """ Textual description of a DWARF expression encoded in 'expr'.
        structs should come from the entity encompassing the expression - it's
        needed to be able to parse it correctly.
    """
    # Since this function can be called a lot, initializing a fresh new
    # ExprDumper per call is expensive. So a rudimentary caching scheme is in
    # place to create only one such dumper per instance of structs.
    cache_key = id(structs)
    if cache_key not in _DWARF_EXPR_DUMPER_CACHE:
        _DWARF_EXPR_DUMPER_CACHE[cache_key] = \
            ExprDumper(structs)
    dwarf_expr_dumper = _DWARF_EXPR_DUMPER_CACHE[cache_key]
    dwarf_expr_dumper.clear()
    dwarf_expr_dumper.process_expr(expr)
    return '(' + dwarf_expr_dumper.get_str() + ')'


def describe_reg_name(regnum, machine_arch=None, default=True):
    """ Provide a textual description for a register name, given its serial
        number. The number is expected to be valid.
    """
    if machine_arch is None:
        machine_arch = _MACHINE_ARCH

    if machine_arch == 'x86':
        return _REG_NAMES_x86[regnum]
    elif machine_arch == 'x64':
        return _REG_NAMES_x64[regnum]
    elif default:
        return 'r%s' % regnum
    else:
        return None

#-------------------------------------------------------------------------------

# The machine architecture. Set globally via set_global_machine_arch
#
_MACHINE_ARCH = None


def _describe_attr_ref(attr, die, section_offset):
    return '<0x%x>' % (attr.value + die.cu.cu_offset)

def _describe_attr_value_passthrough(attr, die, section_offset):
    return attr.value

def _describe_attr_hex(attr, die, section_offset):
    return '0x%x' % (attr.value)

def _describe_attr_hex_addr(attr, die, section_offset):
    return '<0x%x>' % (attr.value)

def _describe_attr_split_64bit(attr, die, section_offset):
    low_word = attr.value & 0xFFFFFFFF
    high_word = (attr.value >> 32) & 0xFFFFFFFF
    return '0x%x 0x%x' % (low_word, high_word)

def _describe_attr_strp(attr, die, section_offset):
    return '(indirect string, offset: 0x%x): %s' % (
        attr.raw_value, bytes2str(attr.value))

def _describe_attr_string(attr, die, section_offset):
    return bytes2str(attr.value)

def _describe_attr_debool(attr, die, section_offset):
    """ To be consistent with readelf, generate 1 for True flags, 0 for False
        flags.
    """
    return '1' if attr.value else '0'

def _describe_attr_present(attr, die, section_offset):
    """ Some forms may simply mean that an attribute is present,
        without providing any value.
    """
    return '1'

def _describe_attr_block(attr, die, section_offset):
    s = '%s byte block: ' % len(attr.value)
    s += ' '.join('%x' % item for item in attr.value) + ' '
    return s


_ATTR_DESCRIPTION_MAP = defaultdict(
    lambda: _describe_attr_value_passthrough, # default_factory

    DW_FORM_ref1=_describe_attr_ref,
    DW_FORM_ref2=_describe_attr_ref,
    DW_FORM_ref4=_describe_attr_ref,
    DW_FORM_ref8=_describe_attr_split_64bit,
    DW_FORM_ref_udata=_describe_attr_ref,
    DW_FORM_ref_addr=_describe_attr_hex_addr,
    DW_FORM_data4=_describe_attr_hex,
    DW_FORM_data8=_describe_attr_hex,
    DW_FORM_addr=_describe_attr_hex,
    DW_FORM_sec_offset=_describe_attr_hex,
    DW_FORM_flag=_describe_attr_debool,
    DW_FORM_data1=_describe_attr_value_passthrough,
    DW_FORM_data2=_describe_attr_value_passthrough,
    DW_FORM_sdata=_describe_attr_value_passthrough,
    DW_FORM_udata=_describe_attr_value_passthrough,
    DW_FORM_string=_describe_attr_string,
    DW_FORM_strp=_describe_attr_strp,
    DW_FORM_block1=_describe_attr_block,
    DW_FORM_block2=_describe_attr_block,
    DW_FORM_block4=_describe_attr_block,
    DW_FORM_block=_describe_attr_block,
    DW_FORM_flag_present=_describe_attr_present,
    DW_FORM_exprloc=_describe_attr_block,
    DW_FORM_ref_sig8=_describe_attr_ref,
)


_DESCR_DW_INL = {
    DW_INL_not_inlined: '(not inlined)',
    DW_INL_inlined: '(inlined)',
    DW_INL_declared_not_inlined: '(declared as inline but ignored)',
    DW_INL_declared_inlined: '(declared as inline and inlined)',
}

_DESCR_DW_LANG = {
    DW_LANG_C89: '(ANSI C)',
    DW_LANG_C: '(non-ANSI C)',
    DW_LANG_Ada83: '(Ada)',
    DW_LANG_C_plus_plus: '(C++)',
    DW_LANG_Cobol74: '(Cobol 74)',
    DW_LANG_Cobol85: '(Cobol 85)',
    DW_LANG_Fortran77: '(FORTRAN 77)',
    DW_LANG_Fortran90: '(Fortran 90)',
    DW_LANG_Pascal83: '(ANSI Pascal)',
    DW_LANG_Modula2: '(Modula 2)',
    DW_LANG_Java: '(Java)',
    DW_LANG_C99: '(ANSI C99)',
    DW_LANG_Ada95: '(ADA 95)',
    DW_LANG_Fortran95: '(Fortran 95)',
    DW_LANG_PLI: '(PLI)',
    DW_LANG_ObjC: '(Objective C)',
    DW_LANG_ObjC_plus_plus: '(Objective C++)',
    DW_LANG_UPC: '(Unified Parallel C)',
    DW_LANG_D: '(D)',
    DW_LANG_Python: '(Python)',
    DW_LANG_Mips_Assembler: '(MIPS assembler)',
    DW_LANG_Upc: '(nified Parallel C)',
    DW_LANG_HP_Bliss: '(HP Bliss)',
    DW_LANG_HP_Basic91: '(HP Basic 91)',
    DW_LANG_HP_Pascal91: '(HP Pascal 91)',
    DW_LANG_HP_IMacro: '(HP IMacro)',
    DW_LANG_HP_Assembler: '(HP assembler)',
}

_DESCR_DW_ATE = {
    DW_ATE_void: '(void)',
    DW_ATE_address: '(machine address)',
    DW_ATE_boolean: '(boolean)',
    DW_ATE_complex_float: '(complex float)',
    DW_ATE_float: '(float)',
    DW_ATE_signed: '(signed)',
    DW_ATE_signed_char: '(signed char)',
    DW_ATE_unsigned: '(unsigned)',
    DW_ATE_unsigned_char: '(unsigned char)',
    DW_ATE_imaginary_float: '(imaginary float)',
    DW_ATE_decimal_float: '(decimal float)',
    DW_ATE_packed_decimal: '(packed_decimal)',
    DW_ATE_numeric_string: '(numeric_string)',
    DW_ATE_edited: '(edited)',
    DW_ATE_signed_fixed: '(signed_fixed)',
    DW_ATE_unsigned_fixed: '(unsigned_fixed)',
    DW_ATE_HP_float80: '(HP_float80)',
    DW_ATE_HP_complex_float80: '(HP_complex_float80)',
    DW_ATE_HP_float128: '(HP_float128)',
    DW_ATE_HP_complex_float128: '(HP_complex_float128)',
    DW_ATE_HP_floathpintel: '(HP_floathpintel)',
    DW_ATE_HP_imaginary_float80: '(HP_imaginary_float80)',
    DW_ATE_HP_imaginary_float128: '(HP_imaginary_float128)',
}

_DESCR_DW_ACCESS = {
    DW_ACCESS_public: '(public)',
    DW_ACCESS_protected: '(protected)',
    DW_ACCESS_private: '(private)',
}

_DESCR_DW_VIS = {
    DW_VIS_local: '(local)',
    DW_VIS_exported: '(exported)',
    DW_VIS_qualified: '(qualified)',
}

_DESCR_DW_VIRTUALITY = {
    DW_VIRTUALITY_none: '(none)',
    DW_VIRTUALITY_virtual: '(virtual)',
    DW_VIRTUALITY_pure_virtual: '(pure virtual)',
}

_DESCR_DW_ID_CASE = {
    DW_ID_case_sensitive: '(case_sensitive)',
    DW_ID_up_case: '(up_case)',
    DW_ID_down_case: '(down_case)',
    DW_ID_case_insensitive: '(case_insensitive)',
}

_DESCR_DW_CC = {
    DW_CC_normal: '(normal)',
    DW_CC_program: '(program)',
    DW_CC_nocall: '(nocall)',
}

_DESCR_DW_ORD = {
    DW_ORD_row_major: '(row major)',
    DW_ORD_col_major: '(column major)',
}

_DESCR_CFI_REGISTER_RULE_TYPE = dict(
    UNDEFINED='u',
    SAME_VALUE='s',
    OFFSET='c',
    VAL_OFFSET='v',
    REGISTER='',
    EXPRESSION='exp',
    VAL_EXPRESSION='vexp',
    ARCHITECTURAL='a',
)

def _make_extra_mapper(mapping, default, default_interpolate_value=False):
    """ Create a mapping function from attribute parameters to an extra
        value that should be displayed.
    """
    def mapper(attr, die, section_offset):
        if default_interpolate_value:
            d = default % attr.value
        else:
            d = default
        return mapping.get(attr.value, d)
    return mapper


def _make_extra_string(s=''):
    """ Create an extra function that just returns a constant string.
    """
    def extra(attr, die, section_offset):
        return s
    return extra


_DWARF_EXPR_DUMPER_CACHE = {}

def _location_list_extra(attr, die, section_offset):
    # According to section 2.6 of the DWARF spec v3, class loclistptr means
    # a location list, and class block means a location expression.
    #
    if attr.form in ('DW_FORM_data4', 'DW_FORM_data8'):
        return '(location list)'
    else:
        return describe_DWARF_expr(attr.value, die.cu.structs)


def _import_extra(attr, die, section_offset):
    # For DW_AT_import the value points to a DIE (that can be either in the
    # current DIE's CU or in another CU, depending on the FORM). The extra
    # information for it is the abbreviation number in this DIE and its tag.
    if attr.form == 'DW_FORM_ref_addr':
        # Absolute offset value
        ref_die_offset = section_offset + attr.value
    else:
        # Relative offset to the current DIE's CU
        ref_die_offset = attr.value + die.cu.cu_offset

    # Now find the CU this DIE belongs to (since we have to find its abbrev
    # table). This is done by linearly scanning through all CUs, looking for
    # one spanning an address space containing the referred DIE's offset.
    for cu in die.dwarfinfo.iter_CUs():
        if cu['unit_length'] + cu.cu_offset > ref_die_offset >= cu.cu_offset:
            # Once we have the CU, we can actually parse this DIE from the
            # stream.
            with preserve_stream_pos(die.stream):
                ref_die = DIE(cu, die.stream, ref_die_offset)
            #print '&&& ref_die', ref_die
            return '[Abbrev Number: %s (%s)]' % (
                ref_die.abbrev_code, ref_die.tag)

    return '[unknown]'


_EXTRA_INFO_DESCRIPTION_MAP = defaultdict(
    lambda: _make_extra_string(''), # default_factory

    DW_AT_inline=_make_extra_mapper(
        _DESCR_DW_INL, '(Unknown inline attribute value: %x',
        default_interpolate_value=True),
    DW_AT_language=_make_extra_mapper(
        _DESCR_DW_LANG, '(Unknown: %x)', default_interpolate_value=True),
    DW_AT_encoding=_make_extra_mapper(_DESCR_DW_ATE, '(unknown type)'),
    DW_AT_accessibility=_make_extra_mapper(
        _DESCR_DW_ACCESS, '(unknown accessibility)'),
    DW_AT_visibility=_make_extra_mapper(
        _DESCR_DW_VIS, '(unknown visibility)'),
    DW_AT_virtuality=_make_extra_mapper(
        _DESCR_DW_VIRTUALITY, '(unknown virtuality)'),
    DW_AT_identifier_case=_make_extra_mapper(
        _DESCR_DW_ID_CASE, '(unknown case)'),
    DW_AT_calling_convention=_make_extra_mapper(
        _DESCR_DW_CC, '(unknown convention)'),
    DW_AT_ordering=_make_extra_mapper(
        _DESCR_DW_ORD, '(undefined)'),
    DW_AT_frame_base=_location_list_extra,
    DW_AT_location=_location_list_extra,
    DW_AT_string_length=_location_list_extra,
    DW_AT_return_addr=_location_list_extra,
    DW_AT_data_member_location=_location_list_extra,
    DW_AT_vtable_elem_location=_location_list_extra,
    DW_AT_segment=_location_list_extra,
    DW_AT_static_link=_location_list_extra,
    DW_AT_use_location=_location_list_extra,
    DW_AT_allocated=_location_list_extra,
    DW_AT_associated=_location_list_extra,
    DW_AT_data_location=_location_list_extra,
    DW_AT_stride=_location_list_extra,
    DW_AT_import=_import_extra,
)

# 8 in a line, for easier counting
_REG_NAMES_x86 = [
    'eax', 'ecx', 'edx', 'ebx', 'esp', 'ebp', 'esi', 'edi',
    'eip', 'eflags', '<none>', 'st0', 'st1', 'st2', 'st3', 'st4',
    'st5', 'st6', 'st7', '<none>', '<none>', 'xmm0', 'xmm1', 'xmm2',
    'xmm3', 'xmm4', 'xmm5', 'xmm6', 'xmm7', 'mm0', 'mm1', 'mm2',
    'mm3', 'mm4', 'mm5', 'mm6', 'mm7', 'fcw', 'fsw', 'mxcsr',
    'es', 'cs', 'ss', 'ds', 'fs', 'gs', '<none>', '<none>', 'tr', 'ldtr'
]

_REG_NAMES_x64 = [
    'rax', 'rdx', 'rcx', 'rbx', 'rsi', 'rdi', 'rbp', 'rsp',
    'r8',  'r9',  'r10', 'r11', 'r12', 'r13', 'r14', 'r15',
    'rip', 'xmm0',  'xmm1',  'xmm2',  'xmm3', 'xmm4', 'xmm5', 'xmm6',
    'xmm7', 'xmm8', 'xmm9', 'xmm10', 'xmm11', 'xmm12', 'xmm13', 'xmm14',
    'xmm15', 'st0', 'st1', 'st2', 'st3', 'st4', 'st5', 'st6',
    'st7', 'mm0', 'mm1', 'mm2', 'mm3', 'mm4', 'mm5', 'mm6',
    'mm7', 'rflags', 'es', 'cs', 'ss', 'ds', 'fs', 'gs',
    '<none>', '<none>', 'fs.base', 'gs.base', '<none>', '<none>', 'tr', 'ldtr',
    'mxcsr', 'fcw', 'fsw'
]


class ExprDumper(GenericExprVisitor):
    """ A concrete visitor for DWARF expressions that dumps a textual
        representation of the complete expression.

        Usage: after creation, call process_expr, and then get_str for a
        semicolon-delimited string representation of the decoded expression.
    """
    def __init__(self, structs):
        super(ExprDumper, self).__init__(structs)
        self._init_lookups()
        self._str_parts = []

    def clear(self):
        self._str_parts = []

    def get_str(self):
        return '; '.join(self._str_parts)

    def _init_lookups(self):
        self._ops_with_decimal_arg = set([
            'DW_OP_const1u', 'DW_OP_const1s', 'DW_OP_const2u', 'DW_OP_const2s',
            'DW_OP_const4u', 'DW_OP_const4s', 'DW_OP_constu', 'DW_OP_consts',
            'DW_OP_pick', 'DW_OP_plus_uconst', 'DW_OP_bra', 'DW_OP_skip',
            'DW_OP_fbreg', 'DW_OP_piece', 'DW_OP_deref_size',
            'DW_OP_xderef_size', 'DW_OP_regx',])

        for n in range(0, 32):
            self._ops_with_decimal_arg.add('DW_OP_breg%s' % n)

        self._ops_with_two_decimal_args = set([
            'DW_OP_const8u', 'DW_OP_const8s', 'DW_OP_bregx', 'DW_OP_bit_piece'])

        self._ops_with_hex_arg = set(
            ['DW_OP_addr', 'DW_OP_call2', 'DW_OP_call4', 'DW_OP_call_ref'])

    def _after_visit(self, opcode, opcode_name, args):
        self._str_parts.append(self._dump_to_string(opcode, opcode_name, args))

    def _dump_to_string(self, opcode, opcode_name, args):
        if len(args) == 0:
            if opcode_name.startswith('DW_OP_reg'):
                regnum = int(opcode_name[9:])
                return '%s (%s)' % (
                    opcode_name,
                    describe_reg_name(regnum, _MACHINE_ARCH))
            else:
                return opcode_name
        elif opcode_name in self._ops_with_decimal_arg:
            if opcode_name.startswith('DW_OP_breg'):
                regnum = int(opcode_name[10:])
                return '%s (%s): %s' % (
                    opcode_name,
                    describe_reg_name(regnum, _MACHINE_ARCH),
                    args[0])
            elif opcode_name.endswith('regx'):
                # applies to both regx and bregx
                return '%s: %s (%s)' % (
                    opcode_name,
                    args[0],
                    describe_reg_name(args[0], _MACHINE_ARCH))
            else:
                return '%s: %s' % (opcode_name, args[0])
        elif opcode_name in self._ops_with_hex_arg:
            return '%s: %x' % (opcode_name, args[0])
        elif opcode_name in self._ops_with_two_decimal_args:
            return '%s: %s %s' % (opcode_name, args[0], args[1])
        else:
            return '<unknown %s>' % opcode_name



