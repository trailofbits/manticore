#-------------------------------------------------------------------------------
# elftools: elf/elffile.py
#
# ELFFile - main class for accessing ELF files
#
# Eli Bendersky (eliben@gmail.com)
# This code is in the public domain
#-------------------------------------------------------------------------------
from ..common.py3compat import BytesIO
from ..common.exceptions import ELFError
from ..common.utils import struct_parse, elf_assert
from ..construct import ConstructError
from .structs import ELFStructs
from .sections import (
        Section, StringTableSection, SymbolTableSection,
        SUNWSyminfoTableSection, NullSection)
from .dynamic import DynamicSection, DynamicSegment
from .relocation import RelocationSection, RelocationHandler
from .gnuversions import (
        GNUVerNeedSection, GNUVerDefSection,
        GNUVerSymSection)
from .segments import Segment, InterpSegment, NoteSegment
from ..dwarf.dwarfinfo import DWARFInfo, DebugSectionDescriptor, DwarfConfig


class ELFFile(object):
    """ Creation: the constructor accepts a stream (file-like object) with the
        contents of an ELF file.

        Accessible attributes:

            stream:
                The stream holding the data of the file - must be a binary
                stream (bytes, not string).

            elfclass:
                32 or 64 - specifies the word size of the target machine

            little_endian:
                boolean - specifies the target machine's endianness

            header:
                the complete ELF file header

            e_ident_raw:
                the raw e_ident field of the header
    """
    def __init__(self, stream):
        self.stream = stream
        self._identify_file()
        self.structs = ELFStructs(
            little_endian=self.little_endian,
            elfclass=self.elfclass)
        self.header = self._parse_elf_header()

        self.stream.seek(0)
        self.e_ident_raw = self.stream.read(16)

        self._file_stringtable_section = self._get_file_stringtable()
        self._section_name_map = None

    def num_sections(self):
        """ Number of sections in the file
        """
        return self['e_shnum']

    def get_section(self, n):
        """ Get the section at index #n from the file (Section object or a
            subclass)
        """
        section_header = self._get_section_header(n)
        return self._make_section(section_header)

    def get_section_by_name(self, name):
        """ Get a section from the file, by name. Return None if no such
            section exists.
        """
        # The first time this method is called, construct a name to number
        # mapping
        #
        if self._section_name_map is None:
            self._section_name_map = {}
            for i, sec in enumerate(self.iter_sections()):
                self._section_name_map[sec.name] = i
        secnum = self._section_name_map.get(name, None)
        return None if secnum is None else self.get_section(secnum)

    def iter_sections(self):
        """ Yield all the sections in the file
        """
        for i in range(self.num_sections()):
            yield self.get_section(i)

    def num_segments(self):
        """ Number of segments in the file
        """
        return self['e_phnum']

    def get_segment(self, n):
        """ Get the segment at index #n from the file (Segment object)
        """
        segment_header = self._get_segment_header(n)
        return self._make_segment(segment_header)

    def iter_segments(self):
        """ Yield all the segments in the file
        """
        for i in range(self.num_segments()):
            yield self.get_segment(i)

    def address_offsets(self, start, size=1):
        """ Yield a file offset for each ELF segment containing a memory region.

            A memory region is defined by the range [start...start+size). The
            offset of the region is yielded.
        """
        end = start + size
        for seg in self.iter_segments():
            if (start >= seg['p_vaddr'] and
                end <= seg['p_vaddr'] + seg['p_filesz']):
                yield start - seg['p_vaddr'] + seg['p_offset']

    def has_dwarf_info(self):
        """ Check whether this file appears to have debugging information.
            We assume that if it has the debug_info section, it has all theother
            required sections as well.
        """
        return bool(self.get_section_by_name(b'.debug_info'))

    def get_dwarf_info(self, relocate_dwarf_sections=True):
        """ Return a DWARFInfo object representing the debugging information in
            this file.

            If relocate_dwarf_sections is True, relocations for DWARF sections
            are looked up and applied.
        """
        # Expect that has_dwarf_info was called, so at least .debug_info is
        # present.
        # Sections that aren't found will be passed as None to DWARFInfo.
        #
        debug_sections = {}
        for secname in (b'.debug_info', b'.debug_abbrev', b'.debug_str',
                        b'.debug_line', b'.debug_frame',
                        b'.debug_loc', b'.debug_ranges'):
            section = self.get_section_by_name(secname)
            if section is None:
                debug_sections[secname] = None
            else:
                debug_sections[secname] = self._read_dwarf_section(
                    section,
                    relocate_dwarf_sections)

        return DWARFInfo(
                config=DwarfConfig(
                    little_endian=self.little_endian,
                    default_address_size=self.elfclass // 8,
                    machine_arch=self.get_machine_arch()),
                debug_info_sec=debug_sections[b'.debug_info'],
                debug_abbrev_sec=debug_sections[b'.debug_abbrev'],
                debug_frame_sec=debug_sections[b'.debug_frame'],
                # TODO(eliben): reading of eh_frame is not hooked up yet
                eh_frame_sec=None,
                debug_str_sec=debug_sections[b'.debug_str'],
                debug_loc_sec=debug_sections[b'.debug_loc'],
                debug_ranges_sec=debug_sections[b'.debug_ranges'],
                debug_line_sec=debug_sections[b'.debug_line'])

    def get_machine_arch(self):
        """ Return the machine architecture, as detected from the ELF header.
            Not all architectures are supported at the moment.
        """
        if self['e_machine'] == 'EM_X86_64':
            return 'x64'
        elif self['e_machine'] in ('EM_386', 'EM_486'):
            return 'x86'
        elif self['e_machine'] == 'EM_ARM':
            return 'ARM'
        elif self['e_machine'] == 'EM_AARCH64':
            return 'AArch64'
        elif self['e_machine'] == 'EM_MIPS':
            return 'MIPS'
        else:
            return '<unknown>'

    #-------------------------------- PRIVATE --------------------------------#

    def __getitem__(self, name):
        """ Implement dict-like access to header entries
        """
        return self.header[name]

    def _identify_file(self):
        """ Verify the ELF file and identify its class and endianness.
        """
        # Note: this code reads the stream directly, without using ELFStructs,
        # since we don't yet know its exact format. ELF was designed to be
        # read like this - its e_ident field is word-size and endian agnostic.
        #
        self.stream.seek(0)
        magic = self.stream.read(4)
        elf_assert( magic in [ b'\x7fCGC', b'\x7fELF' ], 'Magic number does not match' )

        ei_class = self.stream.read(1)
        if ei_class == b'\x01':
            self.elfclass = 32
        elif ei_class == b'\x02':
            self.elfclass = 64
        else:
            raise ELFError('Invalid EI_CLASS %s' % repr(ei_class))

        ei_data = self.stream.read(1)
        if ei_data == b'\x01':
            self.little_endian = True
        elif ei_data == b'\x02':
            self.little_endian = False
        else:
            raise ELFError('Invalid EI_DATA %s' % repr(ei_data))

    def _section_offset(self, n):
        """ Compute the offset of section #n in the file
        """
        return self['e_shoff'] + n * self['e_shentsize']

    def _segment_offset(self, n):
        """ Compute the offset of segment #n in the file
        """
        return self['e_phoff'] + n * self['e_phentsize']

    def _make_segment(self, segment_header):
        """ Create a Segment object of the appropriate type
        """
        segtype = segment_header['p_type']
        if segtype == 'PT_INTERP':
            return InterpSegment(segment_header, self.stream)
        elif segtype == 'PT_DYNAMIC':
            return DynamicSegment(segment_header, self.stream, self)
        elif segtype == 'PT_NOTE':
            return NoteSegment(segment_header, self.stream, self)
        else:
            return Segment(segment_header, self.stream)

    def _get_section_header(self, n):
        """ Find the header of section #n, parse it and return the struct
        """
        return struct_parse(
            self.structs.Elf_Shdr,
            self.stream,
            stream_pos=self._section_offset(n))

    def _get_section_name(self, section_header):
        """ Given a section header, find this section's name in the file's
            string table
        """
        name_offset = section_header['sh_name']
        return self._file_stringtable_section.get_string(name_offset)

    def _make_section(self, section_header):
        """ Create a section object of the appropriate type
        """
        name = self._get_section_name(section_header)
        sectype = section_header['sh_type']

        if sectype == 'SHT_STRTAB':
            return StringTableSection(section_header, name, self.stream)
        elif sectype == 'SHT_NULL':
            return NullSection(section_header, name, self.stream)
        elif sectype in ('SHT_SYMTAB', 'SHT_DYNSYM', 'SHT_SUNW_LDYNSYM'):
            return self._make_symbol_table_section(section_header, name)
        elif sectype == 'SHT_SUNW_syminfo':
            return self._make_sunwsyminfo_table_section(section_header, name)
        elif sectype == 'SHT_GNU_verneed':
            return self._make_gnu_verneed_section(section_header, name)
        elif sectype == 'SHT_GNU_verdef':
            return self._make_gnu_verdef_section(section_header, name)
        elif sectype == 'SHT_GNU_versym':
            return self._make_gnu_versym_section(section_header, name)
        elif sectype in ('SHT_REL', 'SHT_RELA'):
            return RelocationSection(
                section_header, name, self.stream, self)
        elif sectype == 'SHT_DYNAMIC':
            return DynamicSection(section_header, name, self.stream, self)
        else:
            return Section(section_header, name, self.stream)

    def _make_symbol_table_section(self, section_header, name):
        """ Create a SymbolTableSection
        """
        linked_strtab_index = section_header['sh_link']
        strtab_section = self.get_section(linked_strtab_index)
        return SymbolTableSection(
            section_header, name, self.stream,
            elffile=self,
            stringtable=strtab_section)

    def _make_sunwsyminfo_table_section(self, section_header, name):
        """ Create a SUNWSyminfoTableSection
        """
        linked_strtab_index = section_header['sh_link']
        strtab_section = self.get_section(linked_strtab_index)
        return SUNWSyminfoTableSection(
            section_header, name, self.stream,
            elffile=self,
            symboltable=strtab_section)

    def _make_gnu_verneed_section(self, section_header, name):
        """ Create a GNUVerNeedSection
        """
        linked_strtab_index = section_header['sh_link']
        strtab_section = self.get_section(linked_strtab_index)
        return GNUVerNeedSection(
            section_header, name, self.stream,
            elffile=self,
            stringtable=strtab_section)

    def _make_gnu_verdef_section(self, section_header, name):
        """ Create a GNUVerDefSection
        """
        linked_strtab_index = section_header['sh_link']
        strtab_section = self.get_section(linked_strtab_index)
        return GNUVerDefSection(
            section_header, name, self.stream,
            elffile=self,
            stringtable=strtab_section)

    def _make_gnu_versym_section(self, section_header, name):
        """ Create a GNUVerSymSection
        """
        linked_strtab_index = section_header['sh_link']
        strtab_section = self.get_section(linked_strtab_index)
        return GNUVerSymSection(
            section_header, name, self.stream,
            elffile=self,
            symboltable=strtab_section)

    def _get_segment_header(self, n):
        """ Find the header of segment #n, parse it and return the struct
        """
        return struct_parse(
            self.structs.Elf_Phdr,
            self.stream,
            stream_pos=self._segment_offset(n))

    def _get_file_stringtable(self):
        """ Find the file's string table section
        """
        stringtable_section_num = self['e_shstrndx']
        return StringTableSection(
                header=self._get_section_header(stringtable_section_num),
                name='',
                stream=self.stream)

    def _parse_elf_header(self):
        """ Parses the ELF file header and assigns the result to attributes
            of this object.
        """
        return struct_parse(self.structs.Elf_Ehdr, self.stream, stream_pos=0)

    def _read_dwarf_section(self, section, relocate_dwarf_sections):
        """ Read the contents of a DWARF section from the stream and return a
            DebugSectionDescriptor. Apply relocations if asked to.
        """
        self.stream.seek(section['sh_offset'])
        # The section data is read into a new stream, for processing
        section_stream = BytesIO()
        section_stream.write(self.stream.read(section['sh_size']))

        if relocate_dwarf_sections:
            reloc_handler = RelocationHandler(self)
            reloc_section = reloc_handler.find_relocations_for_section(section)
            if reloc_section is not None:
                reloc_handler.apply_section_relocations(
                        section_stream, reloc_section)

        return DebugSectionDescriptor(
                stream=section_stream,
                name=section.name,
                global_offset=section['sh_offset'],
                size=section['sh_size'])
