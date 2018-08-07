import functools
import collections
import re
import logging
from collections import OrderedDict

from ..core.smtlib import Expression, BitVecConstant


def issymbolic(value):
    '''
    Helper to determine whether an object is symbolic (e.g checking
    if data read from memory is symbolic)

    :param object value: object to check
    :return: whether `value` is symbolic
    :rtype: bool
    '''
    return isinstance(value, Expression)


def istainted(arg, taint=None):
    '''
    Helper to determine whether an object if tainted.
    :param arg: a value or Expression
    :param taint: a regular expression matching a taint value (eg. 'IMPORTANT.*'). If None this functions check for any taint value.
    '''

    if not issymbolic(arg):
        return False
    if taint is None:
        return len(arg.taint) != 0
    for arg_taint in arg.taint:
        m = re.match(taint, arg_taint, re.DOTALL | re.IGNORECASE)
        if m:
            return True
    return False


def get_taints(arg, taint=None):
    '''
    Helper to list an object taints.
    :param arg: a value or Expression
    :param taint: a regular expression matching a taint value (eg. 'IMPORTANT.*'). If None this functions check for any taint value.
    '''

    if not issymbolic(arg):
        return
    for arg_taint in arg.taint:
        if taint is not None:
            m = re.match(taint, arg_taint, re.DOTALL | re.IGNORECASE)
            if m:
                yield arg_taint
        else:
            yield arg_taint
    return


def taint_with(arg, taint, value_bits=256, index_bits=256):
    '''
    Helper to taint a value, Fixme this should not taint in place.
    :param arg: a value or Expression
    :param taint: a regular expression matching a taint value (eg. 'IMPORTANT.*'). If None this functions check for any taint value.
    '''
    if not issymbolic(arg):
        if isinstance(arg, int):
            arg = BitVecConstant(value_bits, arg)
    if not issymbolic(arg):
        raise ValueError("type not supported")
    #fixme we should make a copy and taint the copy
    arg._taint = arg.taint | frozenset((taint,))
    return arg


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


class CacheDict(OrderedDict):
    def __init__(self, *args, max_size=30000, flush_perc=30, **kwargs):
        self._max_size = max_size
        self._purge_percent = flush_perc * 0.01
        self._misses = 0
        self._hits = 0
        self._flushes = 0
        super().__init__(*args, **kwargs)

    def __del__(self):
        log = logging.getLogger(self.__class__.__name__)
        log.debug(
            f'DictCache: hits: {self._hits}, misses: {self._misses}, flushes: {self._flushes}, size: {self.__len__()}')

    def __setitem__(self, key, value):
        if len(self) > self._max_size:
            self.flush()
        return super().__setitem__(key, value)

    def __contains__(self, item):
        x = super().__contains__(item)
        if x:
            self._hits += 1
        else:
            self._misses += 1
        return x

    def flush(self):
        self._flushes += 1
        purge_count = int(len(self) * self._purge_percent)
        for i in range(purge_count):
            self.popitem(last=False)
        self._hits -= purge_count
