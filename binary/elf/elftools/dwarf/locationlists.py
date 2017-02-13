#-------------------------------------------------------------------------------
# elftools: dwarf/locationlists.py
#
# DWARF location lists section decoding (.debug_loc)
#
# Eli Bendersky (eliben@gmail.com)
# This code is in the public domain
#-------------------------------------------------------------------------------
import os
from collections import namedtuple

from ..common.utils import struct_parse


LocationEntry = namedtuple('LocationEntry', 'begin_offset end_offset loc_expr')
BaseAddressEntry = namedtuple('BaseAddressEntry', 'base_address')


class LocationLists(object):
    """ A single location list is a Python list consisting of LocationEntry or
        BaseAddressEntry objects.
    """
    def __init__(self, stream, structs):
        self.stream = stream
        self.structs = structs
        self._max_addr = 2 ** (self.structs.address_size * 8) - 1
        
    def get_location_list_at_offset(self, offset):
        """ Get a location list at the given offset in the section.
        """
        self.stream.seek(offset, os.SEEK_SET)
        return self._parse_location_list_from_stream()

    def iter_location_lists(self):
        """ Yield all location lists found in the section.
        """
        # Just call _parse_location_list_from_stream until the stream ends
        self.stream.seek(0, os.SEEK_END)
        endpos = self.stream.tell()

        self.stream.seek(0, os.SEEK_SET)
        while self.stream.tell() < endpos:
            yield self._parse_location_list_from_stream()

    #------ PRIVATE ------#

    def _parse_location_list_from_stream(self):
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
                # Location list entry
                expr_len = struct_parse(
                    self.structs.Dwarf_uint16(''), self.stream)
                loc_expr = [struct_parse(self.structs.Dwarf_uint8(''),
                                         self.stream)
                                for i in range(expr_len)]
                lst.append(LocationEntry(
                    begin_offset=begin_offset,
                    end_offset=end_offset,
                    loc_expr=loc_expr))
        return lst

