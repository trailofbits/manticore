#-------------------------------------------------------------------------------
# elftools: dwarf/dwarfinfo.py
#
# DWARFInfo - Main class for accessing DWARF debug information
#
# Eli Bendersky (eliben@gmail.com)
# This code is in the public domain
#-------------------------------------------------------------------------------
from collections import namedtuple

from ..common.exceptions import DWARFError
from ..common.utils import (struct_parse, dwarf_assert,
                            parse_cstring_from_stream)
from .structs import DWARFStructs
from .compileunit import CompileUnit
from .abbrevtable import AbbrevTable
from .lineprogram import LineProgram
from .callframe import CallFrameInfo
from .locationlists import LocationLists
from .ranges import RangeLists


# Describes a debug section
#
# stream: a stream object containing the data of this section
# name: section name in the container file
# global_offset: the global offset of the section in its container file
# size: the size of the section's data, in bytes
#
# 'name' and 'global_offset' are for descriptional purposes only and
# aren't strictly required for the DWARF parsing to work.
#
DebugSectionDescriptor = namedtuple('DebugSectionDescriptor',
    'stream name global_offset size')


# Some configuration parameters for the DWARF reader. This exists to allow
# DWARFInfo to be independent from any specific file format/container.
#
# little_endian:
#   boolean flag specifying whether the data in the file is little endian
#
# machine_arch:
#   Machine architecture as a string. For example 'x86' or 'x64'
#
# default_address_size:
#   The default address size for the container file (sizeof pointer, in bytes)
#
DwarfConfig = namedtuple('DwarfConfig',
    'little_endian machine_arch default_address_size')


class DWARFInfo(object):
    """ Acts also as a "context" to other major objects, bridging between
        various parts of the debug infromation.
    """
    def __init__(self,
            config,
            debug_info_sec,
            debug_abbrev_sec,
            debug_frame_sec,
            eh_frame_sec,
            debug_str_sec,
            debug_loc_sec,
            debug_ranges_sec,
            debug_line_sec):
        """ config:
                A DwarfConfig object

            debug_*_sec:
                DebugSectionDescriptor for a section. Pass None for sections
                that don't exist. These arguments are best given with
                keyword syntax.
        """
        self.config = config
        self.debug_info_sec = debug_info_sec
        self.debug_abbrev_sec = debug_abbrev_sec
        self.debug_frame_sec = debug_frame_sec
        self.eh_frame_sec = eh_frame_sec
        self.debug_str_sec = debug_str_sec
        self.debug_loc_sec = debug_loc_sec
        self.debug_ranges_sec = debug_ranges_sec
        self.debug_line_sec = debug_line_sec

        # This is the DWARFStructs the context uses, so it doesn't depend on
        # DWARF format and address_size (these are determined per CU) - set them
        # to default values.
        self.structs = DWARFStructs(
            little_endian=self.config.little_endian,
            dwarf_format=32,
            address_size=self.config.default_address_size)

        # Cache for abbrev tables: a dict keyed by offset
        self._abbrevtable_cache = {}

    def iter_CUs(self):
        """ Yield all the compile units (CompileUnit objects) in the debug info
        """
        return self._parse_CUs_iter()

    def get_abbrev_table(self, offset):
        """ Get an AbbrevTable from the given offset in the debug_abbrev
            section.

            The only verification done on the offset is that it's within the
            bounds of the section (if not, an exception is raised).
            It is the caller's responsibility to make sure the offset actually
            points to a valid abbreviation table.

            AbbrevTable objects are cached internally (two calls for the same
            offset will return the same object).
        """
        dwarf_assert(
            offset < self.debug_abbrev_sec.size,
            "Offset '0x%x' to abbrev table out of section bounds" % offset)
        if offset not in self._abbrevtable_cache:
            self._abbrevtable_cache[offset] = AbbrevTable(
                structs=self.structs,
                stream=self.debug_abbrev_sec.stream,
                offset=offset)
        return self._abbrevtable_cache[offset]

    def get_string_from_table(self, offset):
        """ Obtain a string from the string table section, given an offset
            relative to the section.
        """
        return parse_cstring_from_stream(self.debug_str_sec.stream, offset)

    def line_program_for_CU(self, CU):
        """ Given a CU object, fetch the line program it points to from the
            .debug_line section.
            If the CU doesn't point to a line program, return None.
        """
        # The line program is pointed to by the DW_AT_stmt_list attribute of
        # the top DIE of a CU.
        top_DIE = CU.get_top_DIE()
        if 'DW_AT_stmt_list' in top_DIE.attributes:
            return self._parse_line_program_at_offset(
                    top_DIE.attributes['DW_AT_stmt_list'].value, CU.structs)
        else:
            return None

    def has_CFI(self):
        """ Does this dwarf info have a dwarf_frame CFI section?
        """
        return self.debug_frame_sec is not None

    def CFI_entries(self):
        """ Get a list of dwarf_frame CFI entries from the .debug_frame section.
        """
        cfi = CallFrameInfo(
            stream=self.debug_frame_sec.stream,
            size=self.debug_frame_sec.size,
            base_structs=self.structs)
        return cfi.get_entries()

    def has_EH_CFI(self):
        """ Does this dwarf info have a eh_frame CFI section?
        """
        return self.eh_frame_sec is not None

    def EH_CFI_entries(self):
        """ Get a list of eh_frame CFI entries from the .eh_frame section.
        """
        cfi = CallFrameInfo(
            stream=self.eh_frame_sec.stream,
            size=self.eh_frame_sec.size,
            base_structs=self.structs)
        return cfi.get_entries()

    def location_lists(self):
        """ Get a LocationLists object representing the .debug_loc section of
            the DWARF data, or None if this section doesn't exist.
        """
        if self.debug_loc_sec:
            return LocationLists(self.debug_loc_sec.stream, self.structs)
        else:
            return None

    def range_lists(self):
        """ Get a RangeLists object representing the .debug_ranges section of
            the DWARF data, or None if this section doesn't exist.
        """
        if self.debug_ranges_sec:
            return RangeLists(self.debug_ranges_sec.stream, self.structs)
        else:
            return None

    #------ PRIVATE ------#

    def _parse_CUs_iter(self):
        """ Parse CU entries from debug_info. Yield CUs in order of appearance.
        """
        offset = 0
        while offset < self.debug_info_sec.size:
            cu = self._parse_CU_at_offset(offset)
            # Compute the offset of the next CU in the section. The unit_length
            # field of the CU header contains its size not including the length
            # field itself.
            offset = (  offset +
                        cu['unit_length'] +
                        cu.structs.initial_length_field_size())
            yield cu

    def _parse_CU_at_offset(self, offset):
        """ Parse and return a CU at the given offset in the debug_info stream.
        """
        # Section 7.4 (32-bit and 64-bit DWARF Formats) of the DWARF spec v3
        # states that the first 32-bit word of the CU header determines
        # whether the CU is represented with 32-bit or 64-bit DWARF format.
        #
        # So we peek at the first word in the CU header to determine its
        # dwarf format. Based on it, we then create a new DWARFStructs
        # instance suitable for this CU and use it to parse the rest.
        #
        initial_length = struct_parse(
            self.structs.Dwarf_uint32(''), self.debug_info_sec.stream, offset)
        dwarf_format = 64 if initial_length == 0xFFFFFFFF else 32

        # At this point we still haven't read the whole header, so we don't
        # know the address_size. Therefore, we're going to create structs
        # with a default address_size=4. If, after parsing the header, we
        # find out address_size is actually 8, we just create a new structs
        # object for this CU.
        #
        cu_structs = DWARFStructs(
            little_endian=self.config.little_endian,
            dwarf_format=dwarf_format,
            address_size=4)

        cu_header = struct_parse(
            cu_structs.Dwarf_CU_header, self.debug_info_sec.stream, offset)
        if cu_header['address_size'] == 8:
            cu_structs = DWARFStructs(
                little_endian=self.config.little_endian,
                dwarf_format=dwarf_format,
                address_size=8)

        cu_die_offset = self.debug_info_sec.stream.tell()
        dwarf_assert(
            self._is_supported_version(cu_header['version']),
            "Expected supported DWARF version. Got '%s'" % cu_header['version'])
        return CompileUnit(
                header=cu_header,
                dwarfinfo=self,
                structs=cu_structs,
                cu_offset=offset,
                cu_die_offset=cu_die_offset)

    def _is_supported_version(self, version):
        """ DWARF version supported by this parser
        """
        return 2 <= version <= 4

    def _parse_line_program_at_offset(self, debug_line_offset, structs):
        """ Given an offset to the .debug_line section, parse the line program
            starting at this offset in the section and return it.
            structs is the DWARFStructs object used to do this parsing.
        """
        lineprog_header = struct_parse(
            structs.Dwarf_lineprog_header,
            self.debug_line_sec.stream,
            debug_line_offset)

        # Calculate the offset to the next line program (see DWARF 6.2.4)
        end_offset = (  debug_line_offset + lineprog_header['unit_length'] +
                        structs.initial_length_field_size())

        return LineProgram(
            header=lineprog_header,
            stream=self.debug_line_sec.stream,
            structs=structs,
            program_start_offset=self.debug_line_sec.stream.tell(),
            program_end_offset=end_offset)

