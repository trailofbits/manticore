from __future__ import absolute_import  # noqa
from .expression import Expression, Bool, BitVec, Array, BitVecConstant  # noqa
from .constraints import ConstraintSet  # noqa
from .solver import *  # noqa
from . import operators as Operators  # noqa


import logging
logger = logging.getLogger(__name__)

'''
class OperationNotPermited(SolverException):
    def __init__(self):
        super(OperationNotPermited, self).__init__("You cant build this expression")     #no childrens

class ConcretizeException(SolverException):
    def __init__(self, expression):
        super(ConcretizeException, self).__init__("Need to concretize the following and retry\n"+str(expression))     #no childrens
        self.expression = expression
'''


class VisitorException(Exception):
    pass
