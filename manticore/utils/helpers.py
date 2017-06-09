
from ..core.smtlib import Expression

def issymbolic(value):
    '''
    Helper to determine whether an object is symbolic (e.g checking
    if data read from memory is symbolic)

    :param object value: object to check
    :return: whether `value` is symbolic
    :rtype: bool
    '''
    return isinstance(value, Expression)

import functools

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

def pretty_print_results(results):
    '''
    Prettify the results of using manticore to profile some program

    :param ProfilingResults results: The results of profiling, returned from `executor.dump_stats`
    :rtype: string
    '''

    return '\n'.join([ "Total time: {} seconds".format(results.time_elapsed),
                       "Total instructions executed: {}".format(results.instructions_executed),
                       "Average instructions per second: {}".format(results.instructions_executed / results.time_elapsed),
                       "Time spent loading states: {} seconds".format(results.loading_time),
                       "Time spent saving states: {} seconds".format(results.saving_time),
                       "Time spent in solver: {} seconds".format(results.solver_time)])

