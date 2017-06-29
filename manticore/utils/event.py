import inspect
from weakref import WeakSet, WeakKeyDictionary
from types import MethodType

# Inspired by:
# http://code.activestate.com/recipes/577980-improved-signalsslots-implementation-in-python/

class SignalDisconnectedError(RuntimeError):
    pass


def forward_signals(dest, source, arg=False):
    ''' 
        Replicate and forward all the signals from source to dest
    '''
    #Import all signals from state
    for signal_name in source.__dict__:
        signal = getattr(source, signal_name, None)
        if isinstance(signal, Signal):
            proxy = getattr(dest, signal_name, Signal())
            proxy.when(source, signal, arg)
            setattr(dest, signal_name, proxy)

def _manage_signals(obj, enabled):
    ''' 
        Enable or disable all signals at obj
    '''
    #Import all signals from state
    for signal_name in dir(obj):
        signal = getattr(obj, signal_name)
        if isinstance(signal, Signal):
            if enabled:
                signal.enable()
            else:
                signal.disable()


def enable_signals(obj):
    _manage_signals(obj, True)

def disable_signals(obj):
    _manage_signals(obj, False)


class Signal(object):
    '''
    The Signal class is an approximation of Qt's signals+slot system. Each event
    that an object would like to produce requires a Signal() object. All 
    interested parties on the event must register themselves as receivers via
    connect() or the '+=' operator.

    The event source calls emit() to produce an event (or treat it as a
    callable). All registered receivers will receive it, synchronously.
    '''

    def __init__(self, description=None):
        '''
        Create a Signal() object. Pass 'True' to constructor if locking around
        emit() is required.
        '''
        self.description = description
        self._functions = WeakSet()
        self._methods = WeakKeyDictionary()
        self._forwards = WeakKeyDictionary()
        self.disabled = False

    def disable(self):
        self.disabled = True
    def enable(self):
        self.disabled = False
        

    def __len__(self):
        return len(self._functions) + len(self._methods)

    def __call__(self, *args, **kwargs):
        return self.emit(*args, **kwargs)

    def emit(self, *args, **kwargs):
        'Invoke the signal with |args| and |kwargs|'
        results = []

        if self.disabled:
            return results

        for f in self._functions:
            if '__predicate__' in f.__dict__:
                if not f.__dict__['__predicate__']():
                    continue

            results.append(f(*args, **kwargs))

        for obj, funcs in self._methods.items():
            for f in funcs:
                if '__predicate__' in f.__dict__:
                    if not f.__dict__['__predicate__']():
                        continue

                results.append(f(obj, *args, **kwargs))

        return results

    def connect(self, dest, predicate=None):
        '''
        Connect |dest| to the signal. If |predicate| is set, it is treated as a
        nullary callable whose return value determines if the signal is fired.

        NOTE: Passing identical values to multiple invocations of connect() with
        different values of predicate will overwrite previous predicates and
        persist the last-used value.
        
        To achieve a similar effect, wrap |dest| in a function.

        '''
        assert callable(dest)
        if inspect.ismethod(dest):
            obj, impl = dest.__self__, dest.__func__

            if predicate is not None:
                impl.__dict__['__predicate__'] = predicate

            self._methods.setdefault(obj, set()).add(impl)
        else:
            if predicate is not None:
                dest.__dict__['__predicate__'] = predicate

            self._functions.add(dest)

        for signal, methods in self._forwards.items():
            for method in methods:
                signal.connect(method)
        self._forwards.clear()

    def when(self, obj, signal, arg=False):
        ''' This forwards signal from obj '''
        #will reemit forwarded signal prepending obj to arguments 
        if arg:
            method = MethodType(lambda *args, **kwargs: self.emit(*args, **kwargs), obj)
        else:
            method = self.emit
        if len(self):
            signal.connect(method)
        else:
            self._forwards.setdefault(signal, set()).add(method)

    def __iadd__(self, dest):
        self.connect(dest)
        return self

    def disconnect(self, dest):
        try:
            if inspect.ismethod(dest):
                obj, impl = dest.__self__, dest.__func__
                self._methods[obj].remove(impl)
            else:
                self._functions.remove(dest)
        except KeyError:
            raise SignalDisconnectedError()

    def __isub__(self, dest):
        self.disconnect(dest)
        return self

    def reset(self):
        self._functions.clear()
        self._methods.clear()
        self._forwards.clear()

