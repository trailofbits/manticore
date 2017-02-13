#-------------------------------------------------------------------------------
# elftools: dwarf/compileunit.py
#
# DWARF compile unit
#
# Eli Bendersky (eliben@gmail.com)
# This code is in the public domain
#-------------------------------------------------------------------------------
from .die import DIE


class CompileUnit(object):
    """ A DWARF compilation unit (CU).

            A normal compilation unit typically represents the text and data
            contributed to an executable by a single relocatable object file.
            It may be derived from several source files,
            including pre-processed "include files"

        Serves as a container and context to DIEs that describe objects and code
        belonging to a compilation unit.

        CU header entries can be accessed as dict keys from this object, i.e.
           cu = CompileUnit(...)
           cu['version']  # version field of the CU header

        To get the top-level DIE describing the compilation unit, call the
        get_top_DIE method.
    """
    def __init__(self, header, dwarfinfo, structs, cu_offset, cu_die_offset):
        """ header:
                CU header for this compile unit

            dwarfinfo:
                The DWARFInfo context object which created this one

            structs:
                A DWARFStructs instance suitable for this compile unit

            cu_offset:
                Offset in the stream to the beginning of this CU (its header)

            cu_die_offset:
                Offset in the stream of the top DIE of this CU
        """
        self.dwarfinfo = dwarfinfo
        self.header = header
        self.structs = structs
        self.cu_offset = cu_offset
        self.cu_die_offset = cu_die_offset

        # The abbreviation table for this CU. Filled lazily when DIEs are
        # requested.
        self._abbrev_table = None

        # A list of DIEs belonging to this CU. Lazily parsed.
        self._dielist = []

    def dwarf_format(self):
        """ Get the DWARF format (32 or 64) for this CU
        """
        return self.structs.dwarf_format

    def get_abbrev_table(self):
        """ Get the abbreviation table (AbbrevTable object) for this CU
        """
        if self._abbrev_table is None:
            self._abbrev_table = self.dwarfinfo.get_abbrev_table(
                self['debug_abbrev_offset'])
        return self._abbrev_table

    def get_top_DIE(self):
        """ Get the top DIE (which is either a DW_TAG_compile_unit or
            DW_TAG_partial_unit) of this CU
        """
        return self._get_DIE(0)

    def iter_DIEs(self):
        """ Iterate over all the DIEs in the CU, in order of their appearance.
            Note that null DIEs will also be returned.
        """
        self._parse_DIEs()
        return iter(self._dielist)

    #------ PRIVATE ------#

    def __getitem__(self, name):
        """ Implement dict-like access to header entries
        """
        return self.header[name]

    def _get_DIE(self, index):
        """ Get the DIE at the given index
        """
        self._parse_DIEs()
        return self._dielist[index]

    def _parse_DIEs(self):
        """ Parse all the DIEs pertaining to this CU from the stream and shove
            them sequentially into self._dielist.
            Also set the child/sibling/parent links in the DIEs according
            (unflattening the prefix-order of the DIE tree).
        """
        if len(self._dielist) > 0:
            return

        # Compute the boundary (one byte past the bounds) of this CU in the
        # stream
        cu_boundary = ( self.cu_offset +
                        self['unit_length'] +
                        self.structs.initial_length_field_size())

        # First pass: parse all DIEs and place them into self._dielist
        die_offset = self.cu_die_offset
        while die_offset < cu_boundary:
            die = DIE(
                    cu=self,
                    stream=self.dwarfinfo.debug_info_sec.stream,
                    offset=die_offset)
            self._dielist.append(die)
            die_offset += die.size

        # Second pass - unflatten the DIE tree
        self._unflatten_tree()

    def _unflatten_tree(self):
        """ "Unflatten" the DIE tree from it serial representation, by setting
            the child/sibling/parent links of DIEs.

            Assumes self._dielist was already populated by a linear list of DIEs
            read from the stream section
        """
        # the first DIE in the list is the root node
        root = self._dielist[0]
        parentstack = [root]

        for die in self._dielist[1:]:
            if not die.is_null():
                cur_parent = parentstack[-1]
                # This DIE is a child of the current parent
                cur_parent.add_child(die)
                die.set_parent(cur_parent)
                if die.has_children:
                    parentstack.append(die)
            else:
                # parentstack should not be really empty here. However, some
                # compilers generate DWARF that has extra NULLs in the end and
                # we don't want pyelftools to fail parsing them just because of
                # this.
                if len(parentstack) > 0:
                    # end of children for the current parent
                    parentstack.pop()

