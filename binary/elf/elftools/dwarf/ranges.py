#-------------------------------------------------------------------------------
# elftools: dwarf/ranges.py
#
# DWARF ranges section decoding (.debug_ranges)
#
# Eli Bendersky (eliben@gmail.com)
# This code is in the public domain
#-------------------------------------------------------------------------------
import os
from collections import namedtuple

from ..common.utils import struct_parse


RangeEntry = namedtuple('RangeEntry', 'begin_offset end_offset')
BaseAddressEntry = namedtuple('BaseAddressEntry', 'base_address')


class RangeLists(object):
    """ A single range list is a Python list consisting of RangeEntry or
        BaseAddressEntry objects.
    """
    def __init__(self, stream, structs):
        self.stream = stream
        self.structs = structs
        self._max_addr = 2 ** (self.structs.address_size * 8) - 1

    def get_range_list_at_offset(self, offset):
        """ Get a range list at the given offset in the section.
        """
        self.stream.seek(offset, os.SEEK_SET)
        return self._parse_range_list_from_stream()

    def iter_range_lists(self):
        """ Yield all range lists found in the section.
        """
        # Just call _parse_range_list_from_stream until the stream ends
        self.stream.seek(0, os.SEEK_END)
        endpos = self.stream.tell()

        self.stream.seek(0, os.SEEK_SET)
        while self.stream.tell() < endpos:
            yield self._parse_range_list_from_stream()

    #------ PRIVATE ------#

    def _parse_range_list_from_stream(self):
        lst = []
        while True:
            begin_offset = struct_parse(
                self.structs.Dwarf_target_addr(''), self.stream)
            end_offset = struct_parse(
                self.structs.Dwarf_target_addr(''), self.stream)
            if begin_offset == 0 and end_offset == 0:
                # End of list - we're done.
                break
            elif begin_offset == self._max_addr:
                # Base address selection entry
                lst.append(BaseAddressEntry(base_address=end_offset))
            else: 
                # Range entry
                lst.append(RangeEntry(
                    begin_offset=begin_offset,
                    end_offset=end_offset))
        return lst



