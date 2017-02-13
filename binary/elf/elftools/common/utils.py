#-------------------------------------------------------------------------------
# elftools: common/utils.py
#
# Miscellaneous utilities for elftools
#
# Eli Bendersky (eliben@gmail.com)
# This code is in the public domain
#-------------------------------------------------------------------------------
from contextlib import contextmanager
from .exceptions import ELFParseError, ELFError, DWARFError
from .py3compat import int2byte
from ..construct import ConstructError


def bytelist2string(bytelist):
    """ Convert a list of byte values (e.g. [0x10 0x20 0x00]) to a bytes object
        (e.g. b'\x10\x20\x00').
    """
    return b''.join(int2byte(b) for b in bytelist)


def struct_parse(struct, stream, stream_pos=None):
    """ Convenience function for using the given struct to parse a stream.
        If stream_pos is provided, the stream is seeked to this position before
        the parsing is done. Otherwise, the current position of the stream is
        used.
        Wraps the error thrown by construct with ELFParseError.
    """
    try:
        if stream_pos is not None:
            stream.seek(stream_pos)
        return struct.parse_stream(stream)
    except ConstructError as e:
        raise ELFParseError(str(e))


def parse_cstring_from_stream(stream, stream_pos=None):
    """ Parse a C-string from the given stream. The string is returned without
        the terminating \x00 byte. If the terminating byte wasn't found, None
        is returned (the stream is exhausted).
        If stream_pos is provided, the stream is seeked to this position before
        the parsing is done. Otherwise, the current position of the stream is
        used.
        Note: a bytes object is returned here, because this is what's read from
        the binary file.
    """
    if stream_pos is not None:
        stream.seek(stream_pos)
    CHUNKSIZE = 64
    chunks = []
    found = False
    while True:
        chunk = stream.read(CHUNKSIZE)
        end_index = chunk.find(b'\x00')
        if end_index >= 0:
            chunks.append(chunk[:end_index])
            found = True
            break
        else:
            chunks.append(chunk)
        if len(chunk) < CHUNKSIZE:
            break
    return b''.join(chunks) if found else None


def elf_assert(cond, msg=''):
    """ Assert that cond is True, otherwise raise ELFError(msg)
    """
    _assert_with_exception(cond, msg, ELFError)


def dwarf_assert(cond, msg=''):
    """ Assert that cond is True, otherwise raise DWARFError(msg)
    """
    _assert_with_exception(cond, msg, DWARFError)


@contextmanager
def preserve_stream_pos(stream):
    """ Usage:
        # stream has some position FOO (return value of stream.tell())
        with preserve_stream_pos(stream):
            # do stuff that manipulates the stream
        # stream still has position FOO
    """
    saved_pos = stream.tell()
    yield
    stream.seek(saved_pos)


def roundup(num, bits):
    """ Round up a number to nearest multiple of 2^bits. The result is a number
        where the least significant bits passed in bits are 0.
    """
    return (num - 1 | (1 << bits) - 1) + 1

#------------------------- PRIVATE -------------------------

def _assert_with_exception(cond, msg, exception_type):
    if not cond:
        raise exception_type(msg)
