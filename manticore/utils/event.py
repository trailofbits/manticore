import inspect
from weakref import WeakSet, WeakKeyDictionary
from multiprocessing import Manager

# Inspired by:
# http://code.activestate.com/recipes/577980-improved-signalsslots-implementation-in-python/

class SignalDisconnectedError(RuntimeError):
    pass

class Signal(object):
    '''
    The Signal class is an approximation of Qt's signals+slot system. Each event
    that an object would like to produce requires a Signal() object. All 
    interested parties on the event must register themselves as receivers via
    connect() or the '+=' operator.

    The event source calls emit() to produce an event (or treat it as a
    callable). All registered receivers will receive it, synchronously.
    '''

    def __init__(self):
        '''
        Create a Signal() object. Pass 'True' to constructor if locking around
        emit() is required.
        '''
        self._functions = WeakSet()
        self._methods = WeakKeyDictionary()

    def __call__(self, *args, **kwargs):
        return self.emit(*args, **kwargs)

    def emit(self, *args, **kwargs):
        'Invoke the signal with |args| and |kwargs|'
        results = []

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

