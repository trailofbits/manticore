from expression import Expression, Bool, BitVec, Array
from constraints import ConstraintSet
from functools import wraps
from solver import *
import operators as Operators
import math


import logging
logger = logging.getLogger("SMT")

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
