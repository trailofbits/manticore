from __future__ import print_function
from builtins import *
import collections
import sys
import binascii

if sys.version_info[0] == 2:
    from types import IntType, StringType

def issymbolic(value):
    '''
    Helper to determine whether an object is symbolic (e.g checking
    if data read from memory is symbolic)

    :param object value: object to check
    :return: whether `value` is symbolic
    :rtype: bool
    '''
    from ..core.smtlib import Expression
    return isinstance(value, Expression)

def all_ints(ns):
    '''
    Convert a potentially heterogenous sequence to an iterable of ints.
    '''

    for n in ns:
        if isint(n):
            yield n
        elif isbytestr(n):
            if len(n) == 1:
                yield n[0]
            else:
                raise ValueError('received a bytestring with len >1 where int was needed')
        elif isstring(n):
            if len(n) == 1:
                yield ord(n)
            else:
                raise ValueError('received a string with len >1 where int was needed')
        else:
            raise ValueError('received a {} where int was needed'.format(type(n)))

def hex_encode(s):
    if isinstance(s, tuple):
        s = bytes(list(all_ints(s)))
    return binascii.hexlify(s).decode()

def isstring(value):
    '''
    Helper to determine whether an object is string-y, which is nontrivial when targeting Python 2 and 3 at the same
    time.

    :param object value: object to check
    :return: whether `value` can be treated as string
    :rtype: bool
    '''

    # in python3, string types are 'str', 'bytes'
    # in python2, strings are type 'unicode', 'str'
    if sys.version_info[0] == 2:
        # we want to refer to the str type imported by futurize as well as the builtin
        return isinstance(value, (unicode, str, StringType))
    elif sys.version_info[0] == 3:
        return isinstance(value, (str, bytes))

def isunicode(value):
    '''
    Helper to determine whether an object is a unicode string, which is nontrivial when targeting Python 2 and 3 at the same
    time.

    :param object value: object to check
    :return: whether `value` can be treated as string
    :rtype: bool
    '''

    # in python3, string types are 'str', 'bytes'
    # in python2, strings are type 'unicode', 'str'
    if sys.version_info[0] == 2:
        return isinstance(value, unicode)
    elif sys.version_info[0] == 3:
        return isinstance(value, str)

def isbytestr(value):
    '''
    Helper to determine whether an object is a bytestring, which is nontrivial when targeting Python 2 and 3 at the same
    time.

    :param object value: object to check
    :return: whether `value` can be treated as string
    :rtype: bool
    '''

    # in python3, bytestring types are 'bytes'
    # in python2, bytestring types are 'str'
    if sys.version_info[0] == 2:
        return isinstance(value, (str, StringType))
    elif sys.version_info[0] == 3:
        return isinstance(value, bytes)

def isint(value):
    '''
    Helper to determine whether an object is an int, which is nontrivial when targeting Python 2 and 3 at the same
    time.

    :param object value: object to check
    :return: whether `value` can be treated as string
    :rtype: bool
    '''

    if sys.version_info[0] == 2:
        return isinstance(value, (int, long, IntType))
    elif sys.version_info[0] == 3:
        return isinstance(value, int)

def as_unicode(s):
    if isbytestr(s):
        return s.decode()
    elif isstring(s):
        return s
    raise ValueError('expected string-like value, got {}'.format(type(s).__name__))

import functools


class memoized(object):
    '''Decorator. Caches a function's return value each time it is called.
    If called later with the same arguments, the cached value is returned
    (not reevaluated).
    '''

    def __init__(self, func):
        self.func = func
        self.cache = {}

    def __call__(self, *args, **kwargs):
        key = args + tuple(sorted(kwargs.items()))
        if not isinstance(key, collections.Hashable):
            # uncacheable. a list, for instance.
            # better to not cache than blow up.
            return self.func(*args, **kwargs)
        if key in self.cache:
            return self.cache[key]
        else:
            value = self.func(*args, **kwargs)
            self.cache[key] = value
            return value

    def __repr__(self):
        '''Return the function's docstring.'''
        return self.func.__doc__

    def __get__(self, obj, objtype):
        '''Support instance methods.'''
        return functools.partial(self.__call__, obj)


def is_binja_disassembler(disasm):
    return disasm == "binja-il"
