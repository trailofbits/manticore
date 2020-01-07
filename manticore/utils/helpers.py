import logging
import pickle
import sys
from collections import OrderedDict


logger = logging.getLogger(__name__)


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
        try:
            log = logging.getLogger(self.__class__.__name__)
            log.debug(
                f"DictCache: hits: {self._hits}, misses: {self._misses}, flushes: {self._flushes}, size: {self.__len__()}"
            )
        except TypeError:
            # Prevent "TypeError: attribute of type 'NoneType' is not callable" on line 32
            # TODO - figure out why this happens (I think it's only on concrete runs?)
            pass

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
        logger.info("Serializing %s", f.name if hasattr(f, "name") else "<unknown>")
        try:
            f.write(pickle_dumps(state))
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
        logger.info("Deserializing %s", f.name if hasattr(f, "name") else "<unknown>")
        return pickle.load(f)


def pickle_dumps(obj):
    """Consolidates pickling in one place so we can fix the protocol version"""
    return pickle.dumps(obj, protocol=pickle.HIGHEST_PROTOCOL)
