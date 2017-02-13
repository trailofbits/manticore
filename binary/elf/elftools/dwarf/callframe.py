#-------------------------------------------------------------------------------
# elftools: dwarf/callframe.py
#
# DWARF call frame information
#
# Eli Bendersky (eliben@gmail.com)
# This code is in the public domain
#-------------------------------------------------------------------------------
import copy
from collections import namedtuple
from ..common.utils import (struct_parse, dwarf_assert, preserve_stream_pos)
from ..common.py3compat import iterkeys
from .structs import DWARFStructs
from .constants import *


class CallFrameInfo(object):
    """ DWARF CFI (Call Frame Info)

        stream, size:
            A stream holding the .debug_frame section, and the size of the
            section in it.

        base_structs:
            The structs to be used as the base for parsing this section.
            Eventually, each entry gets its own structs based on the initial
            length field it starts with. The address_size, however, is taken
            from base_structs. This appears to be a limitation of the DWARFv3
            standard, fixed in v4.
            A discussion I had on dwarf-discuss confirms this.
            So for DWARFv4 we'll take the address size from the CIE header,
            but for earlier versions will use the elfclass of the containing
            file; more sophisticated methods are used by libdwarf and others,
            such as guessing which CU contains which FDEs (based on their
            address ranges) and taking the address_size from those CUs.
    """
    def __init__(self, stream, size, base_structs):
        self.stream = stream
        self.size = size
        self.base_structs = base_structs
        self.entries = None

        # Map between an offset in the stream and the entry object found at this
        # offset. Useful for assigning CIE to FDEs according to the CIE_pointer
        # header field which contains a stream offset.
        self._entry_cache = {}

    def get_entries(self):
        """ Get a list of entries that constitute this CFI. The list consists
            of CIE or FDE objects, in the order of their appearance in the
            section.
        """
        if self.entries is None:
            self.entries = self._parse_entries()
        return self.entries

    #-------------------------

    def _parse_entries(self):
        entries = []
        offset = 0
        while offset < self.size:
            entries.append(self._parse_entry_at(offset))
            offset = self.stream.tell()
        return entries

    def _parse_entry_at(self, offset):
        """ Parse an entry from self.stream starting with the given offset.
            Return the entry object. self.stream will point right after the
            entry.
        """
        if offset in self._entry_cache:
            return self._entry_cache[offset]

        entry_length = struct_parse(
            self.base_structs.Dwarf_uint32(''), self.stream, offset)
        dwarf_format = 64 if entry_length == 0xFFFFFFFF else 32

        entry_structs = DWARFStructs(
            little_endian=self.base_structs.little_endian,
            dwarf_format=dwarf_format,
            address_size=self.base_structs.address_size)

        # Read the next field to see whether this is a CIE or FDE
        CIE_id = struct_parse(
            entry_structs.Dwarf_offset(''), self.stream)

        is_CIE = (
            (dwarf_format == 32 and CIE_id == 0xFFFFFFFF) or
            CIE_id == 0xFFFFFFFFFFFFFFFF)

        if is_CIE:
            header_struct = entry_structs.Dwarf_CIE_header
        else:
            header_struct = entry_structs.Dwarf_FDE_header

        # Parse the header, which goes up to and including the
        # return_address_register field
        header = struct_parse(
            header_struct, self.stream, offset)

        # If this is DWARF version 4 or later, we can have a more precise
        # address size, read from the CIE header.
        if entry_structs.dwarf_version >= 4:
            entry_structs = DWARFStructs(
                little_endian=entry_structs.little_endian,
                dwarf_format=entry_structs.dwarf_format,
                address_size=header.address_size)

        # For convenience, compute the end offset for this entry
        end_offset = (
            offset + header.length +
            entry_structs.initial_length_field_size())

        # At this point self.stream is at the start of the instruction list
        # for this entry
        instructions = self._parse_instructions(
            entry_structs, self.stream.tell(), end_offset)

        if is_CIE:
            self._entry_cache[offset] = CIE(
                header=header, instructions=instructions, offset=offset,
                structs=entry_structs)
        else: # FDE
            with preserve_stream_pos(self.stream):
                cie = self._parse_entry_at(header['CIE_pointer'])
            self._entry_cache[offset] = FDE(
                header=header, instructions=instructions, offset=offset,
                structs=entry_structs, cie=cie)
        return self._entry_cache[offset]

    def _parse_instructions(self, structs, offset, end_offset):
        """ Parse a list of CFI instructions from self.stream, starting with
            the offset and until (not including) end_offset.
            Return a list of CallFrameInstruction objects.
        """
        instructions = []
        while offset < end_offset:
            opcode = struct_parse(structs.Dwarf_uint8(''), self.stream, offset)
            args = []

            primary = opcode & _PRIMARY_MASK
            primary_arg = opcode & _PRIMARY_ARG_MASK
            if primary == DW_CFA_advance_loc:
                args = [primary_arg]
            elif primary == DW_CFA_offset:
                args = [
                    primary_arg,
                    struct_parse(structs.Dwarf_uleb128(''), self.stream)]
            elif primary == DW_CFA_restore:
                args = [primary_arg]
            # primary == 0 and real opcode is extended
            elif opcode in (DW_CFA_nop, DW_CFA_remember_state,
                            DW_CFA_restore_state):
                args = []
            elif opcode == DW_CFA_set_loc:
                args = [
                    struct_parse(structs.Dwarf_target_addr(''), self.stream)]
            elif opcode == DW_CFA_advance_loc1:
                args = [struct_parse(structs.Dwarf_uint8(''), self.stream)]
            elif opcode == DW_CFA_advance_loc2:
                args = [struct_parse(structs.Dwarf_uint16(''), self.stream)]
            elif opcode == DW_CFA_advance_loc4:
                args = [struct_parse(structs.Dwarf_uint32(''), self.stream)]
            elif opcode in (DW_CFA_offset_extended, DW_CFA_register,
                            DW_CFA_def_cfa, DW_CFA_val_offset):
                args = [
                    struct_parse(structs.Dwarf_uleb128(''), self.stream),
                    struct_parse(structs.Dwarf_uleb128(''), self.stream)]
            elif opcode in (DW_CFA_restore_extended, DW_CFA_undefined,
                            DW_CFA_same_value, DW_CFA_def_cfa_register,
                            DW_CFA_def_cfa_offset):
                args = [struct_parse(structs.Dwarf_uleb128(''), self.stream)]
            elif opcode == DW_CFA_def_cfa_offset_sf:
                args = [struct_parse(structs.Dwarf_sleb128(''), self.stream)]
            elif opcode == DW_CFA_def_cfa_expression:
                args = [struct_parse(
                    structs.Dwarf_dw_form['DW_FORM_block'], self.stream)]
            elif opcode in (DW_CFA_expression, DW_CFA_val_expression):
                args = [
                    struct_parse(structs.Dwarf_uleb128(''), self.stream),
                    struct_parse(
                        structs.Dwarf_dw_form['DW_FORM_block'], self.stream)]
            elif opcode in (DW_CFA_offset_extended_sf,
                            DW_CFA_def_cfa_sf, DW_CFA_val_offset_sf):
                args = [
                    struct_parse(structs.Dwarf_uleb128(''), self.stream),
                    struct_parse(structs.Dwarf_sleb128(''), self.stream)]
            else:
                dwarf_assert(False, 'Unknown CFI opcode: 0x%x' % opcode)

            instructions.append(CallFrameInstruction(opcode=opcode, args=args))
            offset = self.stream.tell()
        return instructions


def instruction_name(opcode):
    """ Given an opcode, return the instruction name.
    """
    primary = opcode & _PRIMARY_MASK
    if primary == 0:
        return _OPCODE_NAME_MAP[opcode]
    else:
        return _OPCODE_NAME_MAP[primary]


class CallFrameInstruction(object):
    """ An instruction in the CFI section. opcode is the instruction
        opcode, numeric - as it appears in the section. args is a list of
        arguments (including arguments embedded in the low bits of some
        instructions, when applicable), decoded from the stream.
    """
    def __init__(self, opcode, args):
        self.opcode = opcode
        self.args = args

    def __repr__(self):
        return '%s (0x%x): %s' % (
            instruction_name(self.opcode), self.opcode, self.args)


class CFIEntry(object):
    """ A common base class for CFI entries.
        Contains a header and a list of instructions (CallFrameInstruction).
        offset: the offset of this entry from the beginning of the section
        cie: for FDEs, a CIE pointer is required
    """
    def __init__(self, header, structs, instructions, offset, cie=None):
        self.header = header
        self.structs = structs
        self.instructions = instructions
        self.offset = offset
        self.cie = cie
        self._decoded_table = None

    def get_decoded(self):
        """ Decode the CFI contained in this entry and return a
            DecodedCallFrameTable object representing it. See the documentation
            of that class to understand how to interpret the decoded table.
        """
        if self._decoded_table is None:
            self._decoded_table = self._decode_CFI_table()
        return self._decoded_table

    def __getitem__(self, name):
        """ Implement dict-like access to header entries
        """
        return self.header[name]

    def _decode_CFI_table(self):
        """ Decode the instructions contained in the given CFI entry and return
            a DecodedCallFrameTable.
        """
        if isinstance(self, CIE):
            # For a CIE, initialize cur_line to an "empty" line
            cie = self
            cur_line = dict(pc=0, cfa=None)
            reg_order = []
        else: # FDE
            # For a FDE, we need to decode the attached CIE first, because its
            # decoded table is needed. Its "initial instructions" describe a
            # line that serves as the base (first) line in the FDE's table.
            cie = self.cie
            cie_decoded_table = cie.get_decoded()
            last_line_in_CIE = copy.copy(cie_decoded_table.table[-1])
            cur_line = copy.copy(last_line_in_CIE)
            cur_line['pc'] = self['initial_location']
            reg_order = copy.copy(cie_decoded_table.reg_order)

        table = []

        # Keeps a stack for the use of DW_CFA_{remember|restore}_state
        # instructions.
        line_stack = []

        def _add_to_order(regnum):
            if regnum not in cur_line:
                reg_order.append(regnum)

        for instr in self.instructions:
            # Throughout this loop, cur_line is the current line. Some
            # instructions add it to the table, but most instructions just
            # update it without adding it to the table.

            name = instruction_name(instr.opcode)

            if name == 'DW_CFA_set_loc':
                table.append(copy.copy(cur_line))
                cur_line['pc'] = instr.args[0]
            elif name in (  'DW_CFA_advance_loc1', 'DW_CFA_advance_loc2',
                            'DW_CFA_advance_loc4', 'DW_CFA_advance_loc'):
                table.append(copy.copy(cur_line))
                cur_line['pc'] += instr.args[0] * cie['code_alignment_factor']
            elif name == 'DW_CFA_def_cfa':
                cur_line['cfa'] = CFARule(
                    reg=instr.args[0],
                    offset=instr.args[1])
            elif name == 'DW_CFA_def_cfa_sf':
                cur_line['cfa'] = CFARule(
                    reg=instr.args[0],
                    offset=instr.args[1] * cie['code_alignment_factor'])
            elif name == 'DW_CFA_def_cfa_register':
                cur_line['cfa'] = CFARule(
                    reg=instr.args[0],
                    offset=cur_line['cfa'].offset)
            elif name == 'DW_CFA_def_cfa_offset':
                cur_line['cfa'] = CFARule(
                    reg=cur_line['cfa'].reg,
                    offset=instr.args[0])
            elif name == 'DW_CFA_def_cfa_expression':
                cur_line['cfa'] = CFARule(expr=instr.args[0])
            elif name == 'DW_CFA_undefined':
                _add_to_order(instr.args[0])
                cur_line[instr.args[0]] = RegisterRule(RegisterRule.UNDEFINED)
            elif name == 'DW_CFA_same_value':
                _add_to_order(instr.args[0])
                cur_line[instr.args[0]] = RegisterRule(RegisterRule.SAME_VALUE)
            elif name in (  'DW_CFA_offset', 'DW_CFA_offset_extended',
                            'DW_CFA_offset_extended_sf'):
                _add_to_order(instr.args[0])
                cur_line[instr.args[0]] = RegisterRule(
                    RegisterRule.OFFSET,
                    instr.args[1] * cie['data_alignment_factor'])
            elif name in ('DW_CFA_val_offset', 'DW_CFA_val_offset_sf'):
                _add_to_order(instr.args[0])
                cur_line[instr.args[0]] = RegisterRule(
                    RegisterRule.VAL_OFFSET,
                    instr.args[1] * cie['data_alignment_factor'])
            elif name == 'DW_CFA_register':
                _add_to_order(instr.args[0])
                cur_line[instr.args[0]] = RegisterRule(
                    RegisterRule.REGISTER,
                    instr.args[1])
            elif name == 'DW_CFA_expression':
                _add_to_order(instr.args[0])
                cur_line[instr.args[0]] = RegisterRule(
                    RegisterRule.EXPRESSION,
                    instr.args[1])
            elif name == 'DW_CFA_val_expression':
                _add_to_order(instr.args[0])
                cur_line[instr.args[0]] = RegisterRule(
                    RegisterRule.VAL_EXPRESSION,
                    instr.args[1])
            elif name in ('DW_CFA_restore', 'DW_CFA_restore_extended'):
                _add_to_order(instr.args[0])
                dwarf_assert(
                    isinstance(self, FDE),
                    '%s instruction must be in a FDE' % name)
                if instr.args[0] in last_line_in_CIE:
                    cur_line[instr.args[0]] = last_line_in_CIE[instr.args[0]]
                else:
                    cur_line.pop(instr.args[0], None)
            elif name == 'DW_CFA_remember_state':
                line_stack.append(cur_line)
            elif name == 'DW_CFA_restore_state':
                cur_line = line_stack.pop()

        # The current line is appended to the table after all instructions
        # have ended, in any case (even if there were no instructions).
        table.append(cur_line)
        return DecodedCallFrameTable(table=table, reg_order=reg_order)


# A CIE and FDE have exactly the same functionality, except that a FDE has
# a pointer to its CIE. The functionality was wholly encapsulated in CFIEntry,
# so the CIE and FDE classes exists separately for identification (instead
# of having an explicit "entry_type" field in CFIEntry).
#
class CIE(CFIEntry):
    pass


class FDE(CFIEntry):
    pass


class RegisterRule(object):
    """ Register rules are used to find registers in call frames. Each rule
        consists of a type (enumeration following DWARFv3 section 6.4.1)
        and an optional argument to augment the type.
    """
    UNDEFINED = 'UNDEFINED'
    SAME_VALUE = 'SAME_VALUE'
    OFFSET = 'OFFSET'
    VAL_OFFSET = 'VAL_OFFSET'
    REGISTER = 'REGISTER'
    EXPRESSION = 'EXPRESSION'
    VAL_EXPRESSION = 'VAL_EXPRESSION'
    ARCHITECTURAL = 'ARCHITECTURAL'

    def __init__(self, type, arg=None):
        self.type = type
        self.arg = arg

    def __repr__(self):
        return 'RegisterRule(%s, %s)' % (self.type, self.arg)


class CFARule(object):
    """ A CFA rule is used to compute the CFA for each location. It either
        consists of a register+offset, or a DWARF expression.
    """
    def __init__(self, reg=None, offset=None, expr=None):
        self.reg = reg
        self.offset = offset
        self.expr = expr

    def __repr__(self):
        return 'CFARule(reg=%s, offset=%s, expr=%s)' % (
            self.reg, self.offset, self.expr)


# Represents the decoded CFI for an entry, which is just a large table,
# according to DWARFv3 section 6.4.1
#
# DecodedCallFrameTable is a simple named tuple to group together the table
# and the register appearance order.
#
# table:
#
# A list of dicts that represent "lines" in the decoded table. Each line has
# some special dict entries: 'pc' for the location/program counter (LOC),
# and 'cfa' for the CFARule to locate the CFA on that line.
# The other entries are keyed by register numbers with RegisterRule values,
# and describe the rules for these registers.
#
# reg_order:
#
# A list of register numbers that are described in the table by the order of
# their appearance.
#
DecodedCallFrameTable = namedtuple(
    'DecodedCallFrameTable', 'table reg_order')


#---------------- PRIVATE ----------------#

_PRIMARY_MASK = 0b11000000
_PRIMARY_ARG_MASK = 0b00111111

# This dictionary is filled by automatically scanning the constants module
# for DW_CFA_* instructions, and mapping their values to names. Since all
# names were imported from constants with `import *`, we look in globals()
_OPCODE_NAME_MAP = {}
for name in list(iterkeys(globals())):
    if name.startswith('DW_CFA'):
        _OPCODE_NAME_MAP[globals()[name]] = name




