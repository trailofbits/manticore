from __future__ import print_function
from builtins import *
from types import StringType
import collections
import sys

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

def isint(value):
    '''
    Helper to determine whether an object is an int, which is nontrivial when targeting Python 2 and 3 at the same
    time.

    :param object value: object to check
    :return: whether `value` can be treated as string
    :rtype: bool
    '''

    if sys.version_info[0] == 2:
        return isinstance(value, (int, long))
    elif sys.version_info[0] == 3:
        return isinstance(value, int)

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
