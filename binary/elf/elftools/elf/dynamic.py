#-------------------------------------------------------------------------------
# elftools: elf/dynamic.py
#
# ELF Dynamic Tags
#
# Mike Frysinger (vapier@gentoo.org)
# This code is in the public domain
#-------------------------------------------------------------------------------
import itertools

from .sections import Section, Symbol
from .segments import Segment
from ..common.exceptions import ELFError
from ..common.utils import struct_parse, parse_cstring_from_stream


class _DynamicStringTable(object):
    """ Bare string table based on values found via ELF dynamic tags and
        loadable segments only.  Good enough for get_string() only.
    """
    def __init__(self, stream, table_offset):
        self._stream = stream
        self._table_offset = table_offset

    def get_string(self, offset):
        """ Get the string stored at the given offset in this string table.
        """
        return parse_cstring_from_stream(self._stream,
                                         self._table_offset + offset)


class DynamicTag(object):
    """ Dynamic Tag object - representing a single dynamic tag entry from a
        dynamic section.

        Allows dictionary-like access to the dynamic structure. For special
        tags (those listed in the _HANDLED_TAGS set below), creates additional
        attributes for convenience. For example, .soname will contain the actual
        value of DT_SONAME (fetched from the dynamic symbol table).
    """
    _HANDLED_TAGS = frozenset(
        ['DT_NEEDED', 'DT_RPATH', 'DT_RUNPATH', 'DT_SONAME',
         'DT_SUNW_FILTER'])

    def __init__(self, entry, stringtable):
        if stringtable is None:
            raise ELFError('Creating DynamicTag without string table')
        self.entry = entry
        if entry.d_tag in self._HANDLED_TAGS:
            setattr(self, entry.d_tag[3:].lower(),
                    stringtable.get_string(self.entry.d_val))

    def __getitem__(self, name):
        """ Implement dict-like access to entries
        """
        return self.entry[name]

    def __repr__(self):
        return '<DynamicTag (%s): %r>' % (self.entry.d_tag, self.entry)

    def __str__(self):
        if self.entry.d_tag in self._HANDLED_TAGS:
            s = '"%s"' % getattr(self, self.entry.d_tag[3:].lower())
        else:
            s = '%#x' % self.entry.d_ptr
        return '<DynamicTag (%s) %s>' % (self.entry.d_tag, s)


class Dynamic(object):
    """ Shared functionality between dynamic sections and segments.
    """
    def __init__(self, stream, elffile, stringtable, position):
        self._stream = stream
        self._elffile = elffile
        self._elfstructs = elffile.structs
        self._num_tags = -1
        self._offset = position
        self._tagsize = self._elfstructs.Elf_Dyn.sizeof()

        # Do not access this directly yourself; use _get_stringtable() instead.
        self._stringtable = stringtable

    def get_table_offset(self, tag_name):
        """ Return the virtual address and file offset of a dynamic table.
        """
        ptr = None
        for tag in self._iter_tags(type=tag_name):
            ptr = tag['d_ptr']
            break

        # If we found a virtual address, locate the offset in the file
        # by using the program headers.
        offset = None
        if ptr:
            offset = next(self._elffile.address_offsets(ptr), None)

        return ptr, offset

    def _get_stringtable(self):
        """ Return a string table for looking up dynamic tag related strings.

            This won't be a "full" string table object, but will at least
            support the get_string() function.
        """
        if self._stringtable:
            return self._stringtable

        # If the ELF has stripped its section table (which is unusual, but
        # perfectly valid), we need to use the dynamic tags to locate the
        # dynamic string table.
        _, table_offset = self.get_table_offset('DT_STRTAB')
        if table_offset is not None:
            self._stringtable = _DynamicStringTable(self._stream, table_offset)
            return self._stringtable

        # That didn't work for some reason.  Let's use the section header
        # even though this ELF is super weird.
        self._stringtable = self._elffile.get_section_by_name(b'.dynstr')
        return self._stringtable

    def _iter_tags(self, type=None):
        """ Yield all raw tags (limit to |type| if specified)
        """
        for n in itertools.count():
            tag = self._get_tag(n)
            if type is None or tag['d_tag'] == type:
                yield tag
            if tag['d_tag'] == 'DT_NULL':
                break

    def iter_tags(self, type=None):
        """ Yield all tags (limit to |type| if specified)
        """
        for tag in self._iter_tags(type=type):
            yield DynamicTag(tag, self._get_stringtable())

    def _get_tag(self, n):
        """ Get the raw tag at index #n from the file
        """
        offset = self._offset + n * self._tagsize
        return struct_parse(
            self._elfstructs.Elf_Dyn,
            self._stream,
            stream_pos=offset)

    def get_tag(self, n):
        """ Get the tag at index #n from the file (DynamicTag object)
        """
        return DynamicTag(self._get_tag(n), self._get_stringtable())

    def num_tags(self):
        """ Number of dynamic tags in the file
        """
        if self._num_tags != -1:
            return self._num_tags

        for n in itertools.count():
            tag = self.get_tag(n)
            if tag.entry.d_tag == 'DT_NULL':
                self._num_tags = n + 1
                return self._num_tags


class DynamicSection(Section, Dynamic):
    """ ELF dynamic table section.  Knows how to process the list of tags.
    """
    def __init__(self, header, name, stream, elffile):
        Section.__init__(self, header, name, stream)
        stringtable = elffile.get_section(header['sh_link'])
        Dynamic.__init__(self, stream, elffile, stringtable, self['sh_offset'])


class DynamicSegment(Segment, Dynamic):
    """ ELF dynamic table segment.  Knows how to process the list of tags.
    """
    def __init__(self, header, stream, elffile):
        # The string table section to be used to resolve string names in
        # the dynamic tag array is the one pointed at by the sh_link field
        # of the dynamic section header.
        # So we must look for the dynamic section contained in the dynamic
        # segment, we do so by searching for the dynamic section whose content
        # is located at the same offset as the dynamic segment
        stringtable = None
        for section in elffile.iter_sections():
            if (isinstance(section, DynamicSection) and
                    section['sh_offset'] == header['p_offset']):
                stringtable = elffile.get_section(section['sh_link'])
                break
        Segment.__init__(self, header, stream)
        Dynamic.__init__(self, stream, elffile, stringtable, self['p_offset'])

    def iter_symbols(self):
        """ Yield all symbols in this dynamic segment. The symbols are usually
            the same as returned by SymbolTableSection.iter_symbols. However,
            in stripped binaries, SymbolTableSection might have been removed.
            This method reads from the mandatory dynamic tag DT_SYMTAB.
        """
        tab_ptr, tab_offset = self.get_table_offset('DT_SYMTAB')
        if tab_ptr is None or tab_offset is None:
            raise ELFError('Segment does not contain DT_SYMTAB.')

        symbol_size = self._elfstructs.Elf_Sym.sizeof()

        # Find closest higher pointer than tab_ptr. We'll use that to mark the
        # end of the symbol table.
        nearest_ptr = None
        for tag in self.iter_tags():
            tag_ptr = tag['d_ptr']
            if tag['d_tag'] == 'DT_SYMENT':
                if symbol_size != tag['d_val']:
                    # DT_SYMENT is the size of one symbol entry. It must be the
                    # same as returned by Elf_Sym.sizeof.
                    raise ELFError('DT_SYMENT (%d) != Elf_Sym (%d).' %
                                   (tag['d_val'], symbol_size))
            if (tag_ptr > tab_ptr and
                    (nearest_ptr is None or nearest_ptr > tag_ptr)):
                nearest_ptr = tag_ptr

        if nearest_ptr is None:
            # Use the end of segment that contains DT_SYMTAB.
            for segment in self._elffile.iter_segments():
                if (segment['p_vaddr'] <= tab_ptr and
                        tab_ptr <= (segment['p_vaddr'] + segment['p_filesz'])):
                    nearest_ptr = segment['p_vaddr'] + segment['p_filesz']

        if nearest_ptr is None:
            raise ELFError('Cannot determine the end of DT_SYMTAB.')

        string_table = self._get_stringtable()
        for i in range((nearest_ptr - tab_ptr) // symbol_size):
            symbol = struct_parse(self._elfstructs.Elf_Sym, self._stream,
                                  i * symbol_size + tab_offset)
            symbol_name = string_table.get_string(symbol['st_name'])
            yield Symbol(symbol, symbol_name)
