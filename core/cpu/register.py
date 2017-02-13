from core.smtlib import Operators, Expression, BitVec, Bool

class Register(object):
    '''Generic variable width register. For 1 bit registers, allows writes
    of types bool and int, but always reads back bools.
    '''

    def __init__(self, width):
        self.width = width
        self.value = 0

    def read(self, nbits=None):
        if isinstance(self.value, (int, long, BitVec)):
            val = Operators.EXTRACT(self.value, 0, nbits or self.width)
            return bool(val) if self.width == 1 else val
        elif isinstance(self.value, Bool):
            return self.value
        else:
            raise Exception('Malformed data in a register')

    def write(self, val, nbits=None):
        if self.width == 1:
            assert isinstance(val, (bool, Expression)) or val in (1, 0)
            self.value = int(val) if isinstance(val, bool) else val
        else:
            val = Operators.EXTRACT(val, 0, nbits or self.width)
            self.value = val
