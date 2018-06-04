from builtins import *
from ..core.smtlib.expression import Expression

def issymbolic(value):
    '''
    Helper to determine whether an object is symbolic (e.g checking
    if data read from memory is symbolic)

    :param object value: object to check
    :return: whether `value` is symbolic
    :rtype: bool
    '''
    return isinstance(value, Expression)

def istainted(arg, taint=None):
    '''
    Helper to determine whether an object if tainted.
    :param arg: a value or Expression
    :param taint: a sepecific taint value (eg. 'IMPORTANT'). If None this fucntions check for any taint value.
    '''

    if not issymbolic(arg):
        return False
    if taint is None:
        return len(arg.taint) != 0
    return taint in arg.taint

