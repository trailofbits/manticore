
from ..core.smtlib import Expression

def issymbolic(value):
    '''
    Helper to determine whether a value read is symbolic.
    '''
    return isinstance(value, Expression)

