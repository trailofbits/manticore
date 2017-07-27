import inspect
from weakref import ref, WeakSet, WeakKeyDictionary, WeakValueDictionary
from types import MethodType

class Eventful(object):
    ''' 
        Abstract class for objects emiting and recieving events
        An eventful object can:
          - publish an event with arbitrary arguments to ist subscribers
          - let foreign objects subcribe their methods to events emited here
          - forward events to/from other eventful objects
    '''
    def __init__(self, *args, **kwargs):
        # A dictionary from "event name" -> callback methods  
        # Note that several methods can be asociated with the same object
        self._signals = dict()
        # a set of sink eventul objects (see forward_events_from())
        self._forwards = WeakKeyDictionary()
        super(Eventful, self).__init__(*args, **kwargs)

    def __setstate__(self, state):
        ''' It wont get serialized by design, user is responsable to reconnect'''
        self._signals = dict()
        self._forwards = WeakKeyDictionary()
        return True

    def __getstate__(self):
        return {}

    def _unref(self, robj):
        # this is called when an object that has subscribed to events emited 
        # here has recently been garbage collected
        # This simply removes all callback methods associated with that object
        # Also if no more callbacks at all for an event name it delets the event entry
        remove = set()
        for name, bucket in self._signals.items():
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

    def publish(self, name, *args, **kwargs):   
        bucket = self._get_signal_bucket(name)
        for obj, methods in bucket.items():
            for callback in methods:
                callback(obj(), *args, **kwargs)

        #The include_source flag indicates to prepend the source of the event in
        # the callback signature. This is set on forward_events_from/to 
        for sink, include_source in self._forwards.items():
            if include_source:
                sink.publish(name, self, *args, **kwargs)
            else:
                sink.publish(name, *args, **kwargs)

    def subscribe(self, name, method):
        assert inspect.ismethod(method)
        obj, callback = method.__self__, method.__func__
        bucket = self._get_signal_bucket(name)
        robj = ref(obj, self._unref)  #see unref() for explanation
        bucket.setdefault(robj, set()).add(callback)

    def forward_events_from(self, source, include_source=False):
        if isinstance(source, Eventful):
            source.forward_events_to(self, include_source=include_source)

    def forward_events_to(self, sink, include_source=False):
        ''' This forwards signal to sink '''
        assert isinstance(sink, Eventful)
        self._forwards[sink] = include_source
