import copy
import inspect
import logging
import functools
from typing import Dict, Set
from itertools import takewhile
from weakref import WeakKeyDictionary, ref
from inspect import isgenerator

logger = logging.getLogger(__name__)


class EventsGatherMetaclass(type):
    """
    Metaclass that is used for Eventful to gather events that classes declare to
    publish.
    """

    def __new__(cls, name, parents, d):
        eventful_sub = super(EventsGatherMetaclass, cls).__new__(cls, name, parents, d)

        bases = inspect.getmro(parents[0])

        if name == "Eventful":
            return eventful_sub

        subclasses = takewhile(lambda c: c is not Eventful, bases)
        relevant_classes = [eventful_sub] + list(subclasses)

        # Add a class that defines '_published_events' classmethod to a dict for
        # later lookup. Aggregate the events of all subclasses.
        relevant_events = set()
        for sub in relevant_classes:
            # Not using hasattr() here because we only want classes where it's explicitly
            # defined.
            if "_published_events" in sub.__dict__:
                relevant_events.update(sub._published_events)
        Eventful.__all_events__[eventful_sub] = relevant_events

        return eventful_sub


class Eventful(object, metaclass=EventsGatherMetaclass):
    """
    Abstract class for objects emitting and receiving events
    An eventful object can:
      - publish an event with arbitrary arguments to its subscribers
      - let foreign objects subscribe their methods to events emitted here
      - forward events to/from other eventful objects

    Any time an Eventful object is deserialized:
      - All previous subscriptions need to be resubscribed
      - All objects that would previously receive forwarded events need to be reconnected
    """

    # Maps an Eventful subclass with a set of all the events it publishes.
    __all_events__: Dict["Eventful", Set[str]] = dict()

    # Set of subscribed events - used as an optimization to only publish events that someone subscribes to
    __sub_events__: Set[str] = set()

    # Set in subclass to advertise the events it plans to publish
    _published_events: Set[str] = set()

    # Event names prefixes
    prefixes = ("will_", "did_", "on_")

    @classmethod
    def all_events(cls):
        """
        Return all events that all subclasses have so far registered to publish.
        """
        all_evts = set()
        for cls, evts in cls.__all_events__.items():
            all_evts.update(evts)
        return all_evts

    @staticmethod
    def will_did(name, can_raise=False):
        """Pre/pos emiting signal"""

        def deco(func):
            @functools.wraps(func)
            def newFunction(self, *args, **kw):
                self._publish(f"will_{name}", *args, can_raise=can_raise, **kw)
                result = func(self, *args, **kw)
                self._publish(f"did_{name}", result, can_raise=can_raise)
                return result

            return newFunction

        return deco

    def __init__(self, *args, **kwargs):
        # A dictionary from "event name" -> callback methods
        # Note that several methods can be associated with the same object
        self._signals = dict()
        # a set of sink eventful objects (see forward_events_from())
        self._forwards = WeakKeyDictionary()
        super().__init__()

    def __setstate__(self, state):
        """It wont get serialized by design, user is responsible to reconnect"""
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
        for name, bucket in self._signals.items():
            if robj in bucket:
                del bucket[robj]
            if len(bucket) == 0:
                remove.add(name)
        for name in remove:
            del self._signals[name]

    def _get_signal_bucket(self, name):
        # Each event name has a bucket of callback methods
        # A bucket is a dictionary obj -> set(method1, method2...)
        return self._signals.setdefault(name, dict())

    def _check_event(self, _name):
        basename = _name
        for prefix in self.prefixes:
            if _name.startswith(prefix):
                basename = _name[len(prefix) :]

        cls = self.__class__
        if basename not in cls.__all_events__[cls]:
            logger.warning("Event '%s' not pre-declared. (self: %s)", _name, repr(self))

    # Wrapper for _publish_impl that also makes sure the event is published from
    # a class that supports it.
    # The underscore _name is to avoid naming collisions with callback params
    def _publish(self, _name, *args, can_raise=True, **kwargs):
        # only publish if there is at least one subscriber
        try:
            if _name in self.__sub_events__:
                self._check_event(_name)
                self._publish_impl(_name, *args, **kwargs)
        except Exception as e:
            logger.warning("Exception raised in callback: %s", e)
            if can_raise:
                raise

    # Separate from _publish since the recursive method call to forward an event
    # shouldn't check the event.
    def _publish_impl(self, _name, *args, **kwargs):
        bucket = self._get_signal_bucket(_name)
        for robj, methods in bucket.items():
            for callback in methods:
                # Need to clone any iterable args, otherwise the first usage will drain it.
                # If the generator isn't available on `self`, give up and return it anyway.
                new_args = (
                    (arg if not isgenerator(arg) else getattr(self, arg.__name__, arg))
                    for arg in args
                )
                callback(robj(), *new_args, **kwargs)

        # The include_source flag indicates to prepend the source of the event in
        # the callback signature. This is set on forward_events_from/to
        items = tuple(self._forwards.items())
        for sink, include_source in items:
            if include_source:
                sink._publish_impl(_name, self, *args, **kwargs)
            else:
                sink._publish_impl(_name, *args, **kwargs)

    def subscribe(self, name, method):
        assert inspect.ismethod(method), f"{method.__class__.__name__} is not a method"
        obj, callback = method.__self__, method.__func__
        bucket = self._get_signal_bucket(name)
        robj = ref(obj, self._unref)  # see unref() for explanation
        bucket.setdefault(robj, set()).add(callback)
        self.__sub_events__.add(name)

    def forward_events_from(self, source: "Eventful", include_source: bool = False) -> None:
        assert isinstance(source, Eventful), f"{source.__class__.__name__} is not Eventful"
        source.forward_events_to(self, include_source=include_source)

    def forward_events_to(self, sink: "Eventful", include_source: bool = False) -> None:
        """This forwards signal to sink"""
        assert isinstance(sink, Eventful), f"{sink.__class__.__name__} is not Eventful"
        self._forwards[sink] = include_source

    def copy_eventful_state(self, new_object: "Eventful"):
        new_object._forwards = copy.copy(self._forwards)
        new_object._signals = copy.copy(self._signals)
