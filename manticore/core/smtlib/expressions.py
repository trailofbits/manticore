from typing import Union, Optional, Dict

class ExpressionException(Exception):
    """
    Expression exception
    """
    pass


class Expression(object):
    """ Abstract Unmutable Taintable Expression. """
    __slots__ = ("_taint",)
    def __init__(self, taint: Union[tuple, frozenset] = ()):
        #if self.__class__ is Expression:
        #    raise TypeError
        super().__init__()
        self._taint = frozenset(taint)
        #print (dir(self))
    def __repr__(self):
        return "<{:s} at {:x}{:s}>".format(type(self).__name__, id(self), self.taint and "-T" or "")

    @property
    def is_tainted(self):
        return len(self._taint) != 0

    @property
    def taint(self):
        return self._taint


class Variable(Expression):
    __slots__ = Expression.__slots__ + ("_name",)
    def __init__(self, name: str, **kwargs):
        #if self.__class__ is Variable:
        #    raise TypeError  # Abstract class
        super().__init__(**kwargs)
        self._name = name

    @property
    def declaration(self):
        pass

    @property
    def name(self):
        return self._name

    def __copy__(self, memo):
        raise ExpressionException("Copying of Variables is not allowed.")

    def __deepcopy__(self, memo):
        raise ExpressionException("Copying of Variables is not allowed.")

    def __repr__(self):
        return "<{:s}({:s}) at {:x}>".format(type(self).__name__, self.name, id(self))


class Constant(Expression):
    __slots__ = Expression.__slots__ + ("_value", )
    def __init__(self, value: Union[bool, int], **kwargs):
        #if self.__class__ is Constant:
        #    raise TypeError
        super().__init__(**kwargs)
        self._value = value

    @property
    def value(self):
        return self._value



if __name__ == "__main__":
    import sys
    x = Expression()
    y = Variable(name="Aa")
    z = Constant(value=1)
    import pdb; pdb.set_trace()