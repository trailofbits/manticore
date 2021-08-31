from copy import copy

from ...core.smtlib import Operators, BitVec, Bool


class Register:
    """
    Generic variable width register. For 1 bit registers, allows writes of types
    bool and int, but always reads back bools.
    """

    def __init__(self, width):
        self.width = width
        self.value = 0

    def is_flag(self):
        return self.width == 1

    def read(self):
        return self.value

    def write(self, val):
        if isinstance(val, (Bool, bool)):
            self.value = val
        elif isinstance(val, BitVec):
            self.value = val.Bool() if self.is_flag() else val
        elif isinstance(val, int):
            self.value = Operators.EXTRACT(val, 0, self.width)
            if self.is_flag():
                self.value = bool(self.value)
        else:
            raise TypeError(f"Cannot store {val.__class__.__name__} in Register")
