import logging
import pickle
import sys
from collections import OrderedDict

import copy
import re


logger = logging.getLogger(__name__)


def issymbolic(value):
    """
    Helper to determine whether an object is symbolic (e.g checking
    if data read from memory is symbolic)

    :param object value: object to check
    :return: whether `value` is symbolic
    :rtype: bool
    """
    from ..core.smtlib import Expression  # prevent circular imports

    return isinstance(value, Expression)


def istainted(arg, taint=None):
    """
    Helper to determine whether an object if tainted.
    :param arg: a value or Expression
    :param taint: a regular expression matching a taint value (eg. 'IMPORTANT.*'). If None, this function checks for any taint value.
    """

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
    """
    Helper to list an object taints.
    :param arg: a value or Expression
    :param taint: a regular expression matching a taint value (eg. 'IMPORTANT.*'). If None, this function checks for any taint value.
    """

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
    """
    Helper to taint a value.
    :param arg: a value or Expression
    :param taint: a regular expression matching a taint value (eg. 'IMPORTANT.*'). If None, this function checks for any taint value.
    """
    from ..core.smtlib import BitVecConstant  # prevent circular imports

    tainted_fset = frozenset((taint,))

    if not issymbolic(arg):
        if isinstance(arg, int):
            arg = BitVecConstant(value_bits, arg)
            arg._taint = tainted_fset
        else:
            raise ValueError("type not supported")

    else:
        arg = copy.copy(arg)
        arg._taint |= tainted_fset

    return arg


def interval_intersection(min1, max1, min2, max2):
    """
    Given two intervals, (min1, max1) and (min2, max2) return their intersecting interval,
    or None if they do not overlap.
    """
    left, right = max(min1, min2), min(max1, max2)
    if left < right:
        return left, right
    return None


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
            f"DictCache: hits: {self._hits}, misses: {self._misses}, flushes: {self._flushes}, size: {self.__len__()}"
        )

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


class StateSerializer:
    """
    StateSerializer can serialize and deserialize :class:`~manticore.core.state.State` objects from and to
    stream-like objects.
    """

    def __init__(self):
        pass

    def serialize(self, state, f):
        raise NotImplementedError

    def deserialize(self, f):
        raise NotImplementedError


class PickleSerializer(StateSerializer):
    DEFAULT_RECURSION: int = 0x10000  # 1M
    MAX_RECURSION: int = 0x1000000  # 16.7M

    def __init__(self):
        super().__init__()
        sys.setrecursionlimit(PickleSerializer.DEFAULT_RECURSION)

    def serialize(self, state, f):
        try:
            f.write(pickle.dumps(state, 2))
        except RuntimeError:
            new_limit = sys.getrecursionlimit() * 2
            if new_limit > PickleSerializer.MAX_RECURSION:
                raise Exception(
                    f"PickleSerializer recursion limit surpassed {PickleSerializer.MAX_RECURSION}, aborting"
                )
            logger.info(f"Recursion soft limit {sys.getrecursionlimit()} hit, increasing")
            sys.setrecursionlimit(new_limit)
            self.serialize(state, f)

    def deserialize(self, f):
        return pickle.load(f)
