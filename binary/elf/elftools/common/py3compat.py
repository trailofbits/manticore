#-------------------------------------------------------------------------------
# elftools: common/py3compat.py
#
# Python 3 compatibility code
#
# Eli Bendersky (eliben@gmail.com)
# This code is in the public domain
#-------------------------------------------------------------------------------
import sys
PY3 = sys.version_info[0] == 3


if PY3:
    import io
    StringIO = io.StringIO
    BytesIO = io.BytesIO

    _iterkeys = "keys"
    _iteritems = "items"
    _itervalues = "values"

    def bytes2str(b): return b.decode('latin-1')
    def str2bytes(s): return s.encode('latin-1')
    def int2byte(i):return bytes((i,))
    def byte2int(b): return b

    ifilter = filter

    maxint = sys.maxsize
else:
    import cStringIO
    StringIO = BytesIO = cStringIO.StringIO

    _iterkeys = "iterkeys"
    _iteritems = "iteritems"
    _itervalues = "itervalues"

    def bytes2str(b): return b
    def str2bytes(s): return s
    int2byte = chr
    byte2int = ord

    from itertools import ifilter

    maxint = sys.maxint


def iterkeys(d):
    """Return an iterator over the keys of a dictionary."""
    return getattr(d, _iterkeys)()

def itervalues(d):
    """Return an iterator over the values of a dictionary."""
    return getattr(d, _itervalues)()

def iteritems(d):
    """Return an iterator over the items of a dictionary."""
    return getattr(d, _iteritems)()

