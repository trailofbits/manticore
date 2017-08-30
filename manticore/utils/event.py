import inspect
from weakref import ref, WeakSet, WeakKeyDictionary, WeakValueDictionary
from types import MethodType

class Eventful(object):
    '''
        Abstract class for objects emitting and receiving events
        An eventful object can:
          - publish an event with arbitrary arguments to its subscribers
          - let foreign objects subscribe their methods to events emitted here
          - forward events to/from other eventful objects
    '''
    def __init__(self, *args, **kwargs):
        # A dictionary from "event name" -> callback methods
        # Note that several methods can be associated with the same object
        self._signals = dict()
        # a set of sink eventful objects (see forward_events_from())
        self._forwards = WeakKeyDictionary()
        super(Eventful, self).__init__(*args, **kwargs)

    def __setstate__(self, state):
        ''' It wont get serialized by design, user is responsible to reconnect'''
        self._signals = dict()
        self._forwards = WeakKeyDictionary()
        return True

    def __getstate__(self):
        return {}

    def _unref(self, robj):
        # this is called when an object that has subscribed to events emitted
        # here has recently been garbage collected
        # This simply removes all callback methods associated with that object
        # Also if no more callbacks at all for an event name it deletes the event entry
        remove = set()
        for name, bucket in self._signals.iteritems():
            if robj in bucket:
                del bucket[robj]
            if len(bucket) == 0:
                remove.add(name)
        for name in remove:
            del self._signals[name]

    def _get_signal_bucket(self, name):
        #Each event name has a bucket of callback methods
        #A bucket is a dictionary obj -> set(method1, method2...)
        return self._signals.setdefault(name,  dict())

    # The underscore _name is to avoid naming collisions with callback params
    def publish(self, _name, *args, **kwargs):
        bucket = self._get_signal_bucket(_name)
        for robj, methods in bucket.items():
            for callback in methods:
                callback(robj(), *args, **kwargs)

        #The include_source flag indicates to prepend the source of the event in
        # the callback signature. This is set on forward_events_from/to
        for sink, include_source in self._forwards.items():
            if include_source:
                sink.publish(_name, self, *args, **kwargs)
            else:
                sink.publish(_name, *args, **kwargs)

    def subscribe(self, name, method):
        if not inspect.ismethod(method):
            raise TypeError
        obj, callback = method.__self__, method.__func__
        bucket = self._get_signal_bucket(name)
        robj = ref(obj, self._unref)  #see unref() for explanation
        bucket.setdefault(robj, set()).add(callback)

    def forward_events_from(self, source, include_source=False):
        if not isinstance(source, Eventful):
            raise TypeError
        source.forward_events_to(self, include_source=include_source)

    def forward_events_to(self, sink, include_source=False):
        ''' This forwards signal to sink '''
        if not isinstance(sink, Eventful):
            raise TypeError
        self._forwards[sink] = include_source
