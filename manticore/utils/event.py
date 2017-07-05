import inspect
from weakref import ref, WeakSet, WeakKeyDictionary, WeakValueDictionary
from types import MethodType


class Eventful(object):
    def __init__(self, *args, **kwargs):
        self._signals = dict()
        self._forwards = WeakKeyDictionary()
        super(Eventful, self).__init__(*args, **kwargs)

    def __setstate__(self, state):
        self._signals = dict()
        self._forwards = WeakKeyDictionary()
        return True

    def __getstate__(self):
        return {}


    def _unref(self, robj):
        remove = set()
        for name, bucket in self._signals.items():
            if robj in bucket:
                del bucket[robj]
            if len(bucket) == 0:
                remove.add(name)
        for name in remove:
            del self._signals[name]

    def _get_signal_bucket(self, name):
        return self._signals.setdefault(name,  dict())

    def publish(self, name, *args, **kwargs):   
        bucket = self._get_signal_bucket(name)
        for obj, methods in bucket.items():
            for callback in methods:
                callback(obj(), *args, **kwargs)
        for sink, include_source in self._forwards.items():
            if include_source:
                sink.publish(name, self, *args, **kwargs)
            else:
                sink.publish(name, *args, **kwargs)

    def subscribe(self, name, method):
        assert inspect.ismethod(method)
        obj, callback = method.__self__, method.__func__
        bucket = self._get_signal_bucket(name)
        robj = ref(obj, self._unref)
        bucket.setdefault(robj, set()).add(callback)

    def forward_events_from(self, source, include_source=False):
        if isinstance(source, Eventful):
            source.forward_events_to(self, include_source=include_source)

    def forward_events_to(self, sink, include_source=False):
        ''' This forwards signal to sink '''
        assert isinstance(sink, Eventful)
        self._forwards[sink] = include_source



if __name__ == '__main__':
    class A(Eventful):
        def callback(self):
            print "CALLBACK", self

    a = A()
    b = A()
    a.subscribe('lala', b.callback)

    a.publish('lala')

    a.publish('lala')

    a.publish('lala')

    del b
    print "del "
    print "S", a._signals.items()

