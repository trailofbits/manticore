import inspect
import logging
from weakref import ref, WeakSet, WeakKeyDictionary, WeakValueDictionary

logger = logging.getLogger(__name__)

class Eventful(object):
    '''
        Abstract class for objects emitting and receiving events
        An eventful object can:
          - publish an event with arbitrary arguments to its subscribers
          - let foreign objects subscribe their methods to events emitted here
          - forward events to/from other eventful objects
    '''
    _published_events = set()

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


    @property
    def published_events(self):
        ''' Returns a set of all the events that can be emitted from this object'''
        #The following is done only once (when class and instance variables are the same)
        if self._published_events is self.__class__._published_events:
            # All subclasses except for last (object)
            for cls in inspect.getmro(self.__class__)[:-1]:
                self._published_events.update(self.__class__._published_events)

        return self._published_events

    def _check_event(self, _name):
        prefixes = ('will_', 'did_', 'on_')
        basename = _name
        for prefix in prefixes:
            if _name.startswith(prefix):
                basename = _name[len(prefix):]
        
        if basename not in self.published_events:
            logger.warning("Event '%s' not pre-declared. (self: %s)", _name, repr(self))


    # The underscore _name is to avoid naming collisions with callback params
    def _publish(self, _name, *args, **kwargs):
        #Enable only if debugging
        self._check_event(_name)
        bucket = self._get_signal_bucket(_name)
        for robj, methods in bucket.iteritems():
            for callback in methods:
                callback(robj(), *args, **kwargs)

        #The include_source flag indicates to prepend the source of the event in
        # the callback signature. This is set on forward_events_from/to
        for sink, include_source in self._forwards.items():
            if include_source:
                sink._publish(_name, self, *args, **kwargs)
            else:
                sink._publish(_name, *args, **kwargs)

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
        sink.published_events.update(self.published_events)
        self._forwards[sink] = include_source
