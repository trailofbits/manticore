""" Module for Symbolic Expression

ConstraintSets are considered a factory for new symbolic variables of type:
BoolVariable, BitVecVariable and ArrayVariable.

Normal python operators are overloaded in each class, complex expressions trees
are built operating over expression variables and constants

    cs = ConstraintSet()
    x = cs.new_bitvec(name="SOMEVARNAME", size=32)
    y = x + 199
    condition1 = y < 1000
    condition1 = x > 0

    cs.add( condition1 )
    cs.add( condition2 )

"""
from abc import ABC, abstractmethod
from functools import reduce
import uuid
import re
import copy
from typing import overload, Union, Optional, Tuple, List, FrozenSet, Dict, Any, Set
from functools import lru_cache


def local_simplify(e):
    from .visitors import simplify as visitor_simplify

    x = visitor_simplify(e)
    if isinstance(e, Bool):
        assert isinstance(x, Bool)
    return x


class ExpressionError(Exception):
    """
    Expression exception
    """

    pass


class XSlotted(type):
    """Metaclass that will propagate slots on multi-inheritance classes
    Every class should define __xslots__ (instead of __slots__)

    class Base(object, metaclass=XSlotted, abstract=True):
        pass

    class A(Base, abstract=True):
        __xslots__ = ('a',)
        pass

    class B(Base, abstract=True):
        __xslots__ = ('b',)
        pass

    class C(A, B):
        pass

    # Normal case / baseline
    class X(object):
        __slots__ = ('a', 'b')

    c = C()
    c.a = 1
    c.b = 2

    x = X()
    x.a = 1
    x.b = 2

    import sys
    print (sys.getsizeof(c),sys.getsizeof(x)) #same value

    """

    def __new__(cls, clsname, bases, attrs, abstract=False):

        xslots = frozenset(attrs.get("__xslots__", ()))
        # merge the xslots of all the bases with the one defined here
        for base in bases:
            xslots = xslots.union(getattr(base, "__xslots__", ()))
        attrs["__xslots__"] = tuple(xslots)
        if abstract:
            attrs["__slots__"] = tuple()
        else:
            attrs["__slots__"] = tuple(map(lambda attr: attr.split("#", 1)[0], attrs["__xslots__"]))
        """
        def h(self):
            print(self.__class__, self.__slots__)
            s = []
            for name in self.__slots__:
                if name in ("_concrete_cache", "_written"):
                    continue
                try:
                    print (name)
                    x = getattr(self, name)
                    hash(x)
                    s.append(name)
                except Exception as e:
                    print ("AAAAAAAAAAAAAAAAAAAAERRR", name, e)
            return hash((clsname, tuple(getattr(self, name) for name in s)))

        attrs["__hash__"] = h
        """
        attrs["__hash__"] = object.__hash__
        # attrs["__hash__"] = lambda self : hash((clsname, tuple(getattr(self, name) for name in self.__slots__ if name not in ("_concrete_cache", "_written"))))
        return super().__new__(cls, clsname, bases, attrs)


class Expression(object, metaclass=XSlotted, abstract=True):
    """ Abstract taintable Expression. """

    __xslots__: Tuple[str, ...] = ("_taint",)

    def __init__(self, *, taint: FrozenSet[str] = frozenset()):
        """
        An abstract Unmutable Taintable Expression
        :param taint: A frozenzset of taints. Normally strings
        """
        self._taint = taint
        super().__init__()

    def __repr__(self):
        return "<{:s} at {:x}{:s}>".format(
            type(self).__name__, id(self), self._taint and "-T" or ""
        )

    @property
    def is_tainted(self) -> bool:
        return bool(self._taint)

    @property
    def taint(self) -> FrozenSet[str]:
        return self._taint

    @property
    def operands(self) -> Optional[Tuple["Expression"]]:
        """ Hack so we can use any Expression as a node """
        ...

    def __getstate__(self):
        return {attr: getattr(self, attr) for attr in self.__slots__}

    def __setstate__(self, state):
        for attr in self.__slots__:
            setattr(self, attr, state[attr])


class Variable(Expression, abstract=True):
    """ Variable is an Expression that has a name """

    __xslots__: Tuple[str, ...] = ("_name",)

    def __init__(self, *, name: str, **kwargs):
        """Variable is an Expression that has a name
        :param name: The Variable name
        """
        super().__init__(**kwargs)
        self._name = name

    @property
    def name(self) -> str:
        return self._name

    def __repr__(self):
        return "<{:s}({:s}) at {:x}>".format(type(self).__name__, self.name, id(self))

    """
    def __eq__(self, other):
        # Ignore the taint for eq comparison
        return self._name==other._name and super().__eq__(other)
    """


class Constant(Expression, abstract=True):
    """ Constants expressions have a concrete python value. """

    __xslots__: Tuple[str, ...] = ("_value",)

    def __init__(self, *, value: Union[bool, int], **kwargs):
        """A constant expression has a value

        :param value: The constant value
        """
        super().__init__(**kwargs)
        self._value = value

    @property
    def value(self):
        return self._value


class Operation(Expression, abstract=True):
    """ Operation expressions contain operands which are also Expressions. """

    __xslots__: Tuple[str, ...] = ("_operands",)

    def __init__(self, *, operands: Tuple[Expression, ...], **kwargs):
        """An operation has operands

        :param operands: A tuple of expression operands
        """
        self._operands = operands
        taint = kwargs.get("taint")
        # If taint was not forced by a keyword argument, calculate default
        if taint is None:
            kwargs["taint"] = frozenset({y for x in operands for y in x.taint})
        super().__init__(**kwargs)

    @property
    def operands(self):
        return self._operands


###############################################################################
# Booleans
class Bool(Expression, abstract=True):
    """Bool expression represent symbolic value of truth"""

    def cast(self, value: Union["Bool", int, bool], **kwargs) -> Union["BoolConstant", "Bool"]:
        """ Cast any type into a Bool or fail """
        if isinstance(value, Bool):
            return value
        return BoolConstant(value=bool(value), **kwargs)

    def __cmp__(self, *args):
        raise NotImplementedError("CMP for Bool")

    def __invert__(self):
        return BoolNot(self)

    def __eq__(self, other):
        # A class that overrides __eq__() and does not define __hash__()
        # will have its __hash__() implicitly set to None.
        return BoolEqual(self, self.cast(other))

    def __ne__(self, other):
        return BoolNot(self == self.cast(other))

    def __and__(self, other):
        return BoolAnd(self, self.cast(other))

    def __or__(self, other):
        return BoolOr(self, self.cast(other))

    def __xor__(self, other):
        return BoolXor(self, self.cast(other))

    def __rand__(self, other):
        return BoolAnd(self.cast(other), self)

    def __ror__(self, other):
        return BoolOr(self.cast(other), self)

    def __rxor__(self, other):
        return BoolXor(self.cast(other), self)

    def __bool__(self):
        raise ExpressionError(
            "You tried to use a Bool Expression as a boolean constant. Expressions could represent a set of concrete values."
        )


class BoolVariable(Bool, Variable):
    pass


class BoolConstant(Bool, Constant):
    def __init__(self, *, value: bool, **kwargs):
        super().__init__(value=bool(value), **kwargs)

    def __bool__(self) -> bool:
        return bool(self._value)


class BoolOperation(Bool, Operation, abstract=True):
    """ It's an operation that results in a Bool """

    pass
    # def __init__(self, *args, **kwargs):
    #    super().__init__(*args, **kwargs)

    # def __xbool__(self):
    #    # FIXME: TODO: re-think is we want to be this forgiving every use of
    #    #  local_simplify looks hacky
    #    simplified = self  # local_simplify(self)
    #    if isinstance(simplified, Constant):
    #        return simplified.value
    #    raise ExpressionError("BoolOperation can not be reduced to a constant")


class BoolNot(BoolOperation):
    def __init__(self, operand: Bool, **kwargs):
        super().__init__(operands=(operand,), **kwargs)


class BoolAnd(BoolOperation):
    def __init__(self, operanda: Bool, operandb: Bool, **kwargs):
        super().__init__(operands=(operanda, operandb), **kwargs)


class BoolOr(BoolOperation):
    def __init__(self, operanda: Bool, operandb: Bool, **kwargs):
        super().__init__(operands=(operanda, operandb), **kwargs)


class BoolXor(BoolOperation):
    def __init__(self, operanda: Bool, operandb: Bool, **kwargs):
        super().__init__(operands=(operanda, operandb), **kwargs)


class BoolITE(BoolOperation):
    def __init__(self, cond: Bool, true: Bool, false: Bool, **kwargs):
        super().__init__(operands=(cond, true, false), **kwargs)


class BitVec(Expression, abstract=True):
    """ BitVector expressions have a fixed bit size """

    __xslots__: Tuple[str, ...] = ("_size",)

    def __init__(self, size: int, **kwargs):
        """This is bit vector expression

        :param size: number of buts used
        """
        super().__init__(**kwargs)
        self._size = size

    @property
    def size(self) -> int:
        return self._size

    @property
    def mask(self) -> int:
        return (1 << self.size) - 1

    @property
    def signmask(self) -> int:
        return 1 << (self.size - 1)

    def cast(self, value: Union["BitVec", str, int, bytes], **kwargs) -> "BitVec":
        """ Cast a value int a BitVec """
        if isinstance(value, BitVec):
            if value.size != self.size:
                raise ExpressionError("BitVector of unexpected size")
            return value
        if isinstance(value, (str, bytes)) and len(value) == 1:
            value = ord(value)
        # Try to support not Integral types that can be casted to int
        value = int(value) & self.mask
        if not isinstance(value, int):
            raise ExpressionError("Not cast-able to BitVec")
        return BitVecConstant(self.size, value, **kwargs)

    def __add__(self, other):
        return BitVecAdd(self, self.cast(other))

    def __sub__(self, other):
        return BitVecSub(self, self.cast(other))

    def __mul__(self, other):
        return BitVecMul(self, self.cast(other))

    def __mod__(self, other):
        return BitVecMod(self, self.cast(other))

    # object.__divmod__(self, other)
    # object.__pow__(self, other[, modulo])

    def __lshift__(self, other):
        return BitVecShiftLeft(self, self.cast(other))

    def __rshift__(self, other):
        return BitVecShiftRight(self, self.cast(other))

    def __and__(self, other):
        return BitVecAnd(self, self.cast(other))

    def __xor__(self, other):
        return BitVecXor(self, self.cast(other))

    def __or__(self, other):
        return BitVecOr(self, self.cast(other))

    # The division operator (/) is implemented by these methods. The
    # __truediv__() method is used when __future__.division is in effect,
    # otherwise __div__() is used. If only one of these two methods is
    # defined, the object will not support division in the alternate context;
    # TypeError will be raised instead.

    def __div__(self, other):
        return BitVecDiv(self, self.cast(other))

    def __truediv__(self, other):
        return BitVecDiv(self, self.cast(other))

    def __floordiv__(self, other):
        return self / other

    # These methods are called to implement the binary arithmetic operations
    # (+, # -, *, /, %, divmod(), pow(), **, <<, >>, &, ^, |) with reflected
    # (swapped) operands. These functions are only called if the left operand
    # does not support the corresponding operation and the operands are of
    # different types. [2] For instance, to evaluate the expression x - y,
    # where y is an instance of a class that has an __rsub__() method,
    # y.__rsub__(x) is called if x.__sub__(y) returns NotImplemented.

    def __radd__(self, other):
        return BitVecAdd(self.cast(other), self)

    def __rsub__(self, other):
        return BitVecSub(self.cast(other), self)

    def __rmul__(self, other):
        return BitVecMul(self.cast(other), self)

    def __rmod__(self, other):
        return BitVecMod(self.cast(other), self)

    def __rtruediv__(self, other):
        return BitVecDiv(self.cast(other), self)

    def __rdiv__(self, other):
        return BitVecDiv(self.cast(other), self)

    # object.__rdivmod__(self, other)
    # object.__rpow__(self, other)

    def __rlshift__(self, other):
        return BitVecShiftLeft(self.cast(other), self)

    def __rrshift__(self, other):
        return BitVecShiftRight(self.cast(other), self)

    def __rand__(self, other):
        return BitVecAnd(self.cast(other), self)

    def __rxor__(self, other):
        return BitVecXor(self.cast(other), self)

    def __ror__(self, other):
        return BitVecOr(self.cast(other), self)

    def __invert__(self):
        return BitVecXor(self, self.cast(self.mask))

    # These are the so-called "rich comparison" methods, and are called
    # for comparison operators in preference to __cmp__() below. The
    # correspondence between operator symbols and method names is as
    # follows:
    #   x<y calls x.__lt__(y),
    #   x<=y calls x.__le__(y),
    #   x==y calls x.__eq__(y),
    #   x!=y and x<>y call x.__ne__(y),
    #   x>y calls x.__gt__(y), and
    #   x>=y calls x.__ge__(y).

    def __lt__(self, other):
        return BoolLessThan(operanda=self, operandb=self.cast(other))

    def __le__(self, other):
        return BoolLessOrEqualThan(self, self.cast(other))

    def __eq__(self, other):
        # A class that overrides __eq__() and does not define __hash__()
        # will have its __hash__() implicitly set to None.
        return BoolEqual(self, self.cast(other))

    def __ne__(self, other):
        # A class that overrides __eq__() and does not define __hash__()
        # will have its __hash__() implicitly set to None.
        return BoolNot(BoolEqual(self, self.cast(other)))

    def __gt__(self, other):
        return BoolGreaterThan(self, self.cast(other))

    def __ge__(self, other):
        return BoolGreaterOrEqualThan(self, self.cast(other))

    def __neg__(self):
        return BitVecNeg(self)

    # Unsigned comparisons
    def ugt(self, other):
        return BoolUnsignedGreaterThan(self, self.cast(other))

    def uge(self, other):
        return BoolUnsignedGreaterOrEqualThan(self, self.cast(other))

    def ult(self, other):
        return BoolUnsignedLessThan(self, self.cast(other))

    def ule(self, other):
        return BoolUnsignedLessOrEqualThan(self, self.cast(other))

    def udiv(self, other):
        return BitVecUnsignedDiv(self, self.cast(other))

    def rudiv(self, other):
        return BitVecUnsignedDiv(self.cast(other), self)

    def sdiv(self, other):
        return BitVecDiv(self, self.cast(other))

    def rsdiv(self, other):
        return BitVecDiv(self.cast(other), self)

    def srem(self, other):
        return BitVecRem(self, self.cast(other))

    def rsrem(self, other):
        return BitVecRem(self.cast(other), self)

    def urem(self, other):
        return BitVecUnsignedRem(self, self.cast(other))

    def rurem(self, other):
        return BitVecUnsignedRem(self.cast(other), self)

    def sar(self, other):
        return BitVecArithmeticShiftRight(self, self.cast(other))

    def sal(self, other):
        return BitVecArithmeticShiftLeft(self, self.cast(other))

    def Bool(self):
        return self != 0


class BitVecVariable(BitVec, Variable):
    pass


class BitVecConstant(BitVec, Constant):
    def __init__(self, size: int, value: int, **kwargs):
        """ A bitvector constant """
        value &= (1 << size) - 1  # Can not use self.mask yet
        super().__init__(size=size, value=value, **kwargs)

    def __bool__(self) -> bool:
        return bool(self.value)

    def __int__(self) -> int:
        return self.value

    @property
    def signed_value(self) -> int:
        """ Gives signed python int representation """
        if self._value & self.signmask:
            return self._value - (1 << self.size)
        else:
            return self._value

    def __eq__(self, other):
        """ If tainted keep a tainted symbolic value"""
        if self.taint:
            return BoolEqual(self, self.cast(other))
        # Ignore the taint for eq comparison
        return self._value == other

    def __repr__(self):
        return f"BitVecConstant<{self.size}, {self.value}>"


class BitVecOperation(BitVec, Operation, abstract=True):
    """ Operations that result in a BitVec """

    def __init__(self, *, operands: Tuple[Expression, ...], **kwargs):
        super().__init__(operands=operands, **kwargs)


class BitVecAdd(BitVecOperation):
    def __init__(self, operanda: BitVec, operandb: BitVec, **kwargs):
        assert operanda.size == operandb.size
        super().__init__(size=operanda.size, operands=(operanda, operandb), **kwargs)


class BitVecSub(BitVecOperation):
    def __init__(self, operanda, operandb, **kwargs):
        super().__init__(size=operanda.size, operands=(operanda, operandb), **kwargs)


class BitVecMul(BitVecOperation):
    def __init__(self, operanda, operandb, **kwargs):
        super().__init__(size=operanda.size, operands=(operanda, operandb), **kwargs)


class BitVecDiv(BitVecOperation):
    def __init__(self, operanda, operandb, **kwargs):
        super().__init__(size=operanda.size, operands=(operanda, operandb), **kwargs)


class BitVecUnsignedDiv(BitVecOperation):
    def __init__(self, operanda, operandb, **kwargs):
        super().__init__(size=operanda.size, operands=(operanda, operandb), **kwargs)


class BitVecMod(BitVecOperation):
    def __init__(self, operanda, operandb, **kwargs):
        super().__init__(size=operanda.size, operands=(operanda, operandb), **kwargs)


class BitVecRem(BitVecOperation):
    def __init__(self, operanda, operandb, **kwargs):
        super().__init__(size=operanda.size, operands=(operanda, operandb), **kwargs)


class BitVecUnsignedRem(BitVecOperation):
    def __init__(self, operanda, operandb, **kwargs):
        super().__init__(size=operanda.size, operands=(operanda, operandb), **kwargs)


class BitVecShiftLeft(BitVecOperation):
    def __init__(self, operanda, operandb, **kwargs):
        super().__init__(size=operanda.size, operands=(operanda, operandb), **kwargs)


class BitVecShiftRight(BitVecOperation):
    def __init__(self, operanda, operandb, **kwargs):
        super().__init__(size=operanda.size, operands=(operanda, operandb), **kwargs)


class BitVecArithmeticShiftLeft(BitVecOperation):
    def __init__(self, operanda, operandb, **kwargs):
        super().__init__(size=operanda.size, operands=(operanda, operandb), **kwargs)


class BitVecArithmeticShiftRight(BitVecOperation):
    def __init__(self, operanda, operandb, **kwargs):
        super().__init__(size=operanda.size, operands=(operanda, operandb), **kwargs)


class BitVecAnd(BitVecOperation):
    def __init__(self, operanda, operandb, *args, **kwargs):
        super().__init__(size=operanda.size, operands=(operanda, operandb), **kwargs)


class BitVecOr(BitVecOperation):
    def __init__(self, operanda: BitVec, operandb: BitVec, *args, **kwargs):
        super().__init__(size=operanda.size, operands=(operanda, operandb), **kwargs)


class BitVecXor(BitVecOperation):
    def __init__(self, operanda, operandb, **kwargs):
        super().__init__(size=operanda.size, operands=(operanda, operandb), **kwargs)


class BitVecNot(BitVecOperation):
    def __init__(self, operanda, **kwargs):
        super().__init__(size=operanda.size, operands=(operanda,), **kwargs)


class BitVecNeg(BitVecOperation):
    def __init__(self, operanda, **kwargs):
        super().__init__(size=operanda.size, operands=(operanda,), **kwargs)


# Comparing two bitvectors results in a Bool
class BoolLessThan(BoolOperation):
    def __init__(self, operanda: BitVec, operandb: BitVec, **kwargs):
        super().__init__(operands=(operanda, operandb), **kwargs)


class BoolLessOrEqualThan(BoolOperation):
    def __init__(self, operanda: BitVec, operandb: BitVec, **kwargs):
        super().__init__(operands=(operanda, operandb), **kwargs)


class BoolEqual(BoolOperation):
    @overload
    def __init__(self, operanda: BitVec, operandb: BitVec, **kwargs):
        ...

    @overload
    def __init__(self, operanda: Bool, operandb: Bool, **kwargs):
        ...

    @overload
    def __init__(self, operanda: "Array", operandb: "Array", **kwargs):
        ...

    def __init__(self, operanda, operandb, **kwargs):
        super().__init__(operands=(operanda, operandb), **kwargs)


class BoolGreaterThan(BoolOperation):
    def __init__(self, operanda: BitVec, operandb: BitVec, **kwargs):
        super().__init__(operands=(operanda, operandb), **kwargs)


class BoolGreaterOrEqualThan(BoolOperation):
    def __init__(self, operanda: BitVec, operandb: BitVec, *args, **kwargs):
        super().__init__(operands=(operanda, operandb), **kwargs)


class BoolUnsignedLessThan(BoolOperation):
    def __init__(self, operanda: BitVec, operandb: BitVec, **kwargs):
        super().__init__(operands=(operanda, operandb), **kwargs)


class BoolUnsignedLessOrEqualThan(BoolOperation):
    def __init__(self, operanda: BitVec, operandb: BitVec, **kwargs):
        super().__init__(operands=(operanda, operandb), **kwargs)


class BoolUnsignedGreaterThan(BoolOperation):
    def __init__(self, operanda, operandb, *args, **kwargs):
        super().__init__(operands=(operanda, operandb), **kwargs)


class BoolUnsignedGreaterOrEqualThan(BoolOperation):
    def __init__(self, operanda, operandb, **kwargs):
        super(BoolUnsignedGreaterOrEqualThan, self).__init__(
            operands=(operanda, operandb), **kwargs
        )


class Array(Expression, abstract=True):
    """An Array expression is an unmutable mapping from bitvector to bitvector

    array.index_size is the number of bits used for addressing a value
    array.value_size is the number of bits used in the values
    array.length counts the valid indexes starting at 0. Accessing outside the bound is undefined

    """

    @property
    @abstractmethod
    def index_size(self) -> int:
        """ The bit size of the index part. Must be overloaded by a more specific class"""
        ...

    @property
    def value_size(self) -> int:
        """ The bit size of the value part. Must be overloaded by a more specific class"""
        raise NotImplementedError

    @property
    def length(self) -> int:
        """ Number of defined items. Must be overloaded by a more specific class"""
        raise NotImplementedError

    def select(self, index) -> Union[BitVec, int]:
        """ Gets a bitvector element from the Array que la"""
        raise NotImplementedError

    def store(self, index, value) -> "Array":
        """ Create a new array that contains the updated value"""
        raise NotImplementedError

    @property
    def default(self) -> Optional[Union[BitVec, int]]:
        """If defined, reading from an uninitialized index return the default value.
        Otherwise, reading from an uninitialized index gives a symbol (normal Array behavior)
        """
        raise NotImplementedError

    @property
    def written(self):
        """Returns the set of potentially symbolic indexes that were written in
        this array.

        Note that as you could overwrite an index so this could have more elements
        than total elements in the array.
        """
        raise NotImplementedError

    def is_known(self, index) -> Union[Bool, bool]:
        """ Returned Boolean Expression holds when the index was used"""
        raise NotImplementedError

    # Following methods are implemented on top of the abstract methods ^
    def in_bounds(self, index: Union[BitVec, int]) -> Union[Bool, bool]:
        """ True if the index points inside the array (or array is unbounded)"""
        if self.length is not None:
            return 0 <= index < self.length
        return True

    def __len__(self):
        """ Number of values. """
        return self.length

    def cast(self, array) -> "Array":
        """Builds an Array from bytes or bytearray
        FIXME: this assigns a random name to a new variable and does not use
        a ConstraintSet as a Factory
        """
        if isinstance(array, Array):
            return array
        arr = ArrayVariable(
            index_size=self.index_size,
            length=len(array),
            default=0,
            value_size=self.value_size,
            name=f"cast{uuid.uuid1()}",
        )
        for pos, byte in enumerate(array):
            arr = arr.store(pos, byte)
        return arr

    def cast_index(self, index: Union[int, BitVec]) -> BitVec:
        """Forgiving casting method that will translate compatible values into
        a compliant BitVec for indexing"""
        if isinstance(index, int):
            return BitVecConstant(self.index_size, index)
        if not isinstance(index, BitVec) or index.size != self.index_size:
            raise ExpressionError(f"Expected BitVector of size {self.index_size}")
        if isinstance(index, Constant):
            return index
        return local_simplify(index)

    def cast_value(self, value: Union[BitVec, bytes, int]) -> BitVec:
        """Forgiving casting method that will translate compatible values into
        a compliant BitVec to be used as a value"""
        if not isinstance(value, (BitVec, bytes, int)):
            raise TypeError
        if isinstance(value, BitVec):
            if value.size != self.value_size:
                raise ValueError
            return value
        if isinstance(value, bytes) and len(value) == 1:
            value = ord(value)
        if not isinstance(value, int):
            value = int(value)
        return BitVecConstant(self.value_size, value)

    def write(self, offset: Union[BitVec, int], buf: Union["Array", bytes]) -> "Array":
        """Builds a new unmutable Array instance on top of current array by
        writing buf at offset"""
        array = self
        for i, value in enumerate(buf):
            array = array.store(offset + i, value)
        return array

    def read(self, offset: int, size: int) -> "Array":
        """ A projection of the current array. """
        return ArraySlice(self, offset=offset, size=size)

    @overload
    def __getitem__(self, index: Union[BitVec, int]) -> Union[BitVec, int]:
        ...

    @overload
    def __getitem__(self, index: slice) -> "Array":
        ...

    def __getitem__(self, index):
        """__getitem__ allows for pythonic access
        A = ArrayVariable(index_size=32, value_size=8)
        A[10] := a symbol representing the value under index 10 in array A
        A[10:20] := a symbol representing a slice of array A
        """
        if isinstance(index, slice):
            start, stop, size = self._fix_slice(index)
            return self.read(start, size)
        return self.select(index)

    def __iter__(self):
        """ In a bounded array iterates over all elements. """
        for i in range(len(self)):
            yield self[i]

    @staticmethod
    def _compare_buffers(a: "Array", b: "Array") -> Bool:
        """ Builds an expression that represents equality between the two arrays."""
        if a.length != b.length:
            return BoolConstant(value=False)
        cond: Bool = BoolConstant(value=True)
        for i in range(a.length):
            cond = BoolAnd(cond.cast(a[i] == b[i]), cond)
            if cond is BoolConstant(value=False):
                return BoolConstant(value=False)
        return cond

    def __eq__(self, other):
        """If both arrays has the same elements they are equal.
        The difference in taints are ignored."""
        return self._compare_buffers(self, self.cast(other))

    def __ne__(self, other):
        return BoolNot(self == other)

    def _fix_slice(self, index: slice):
        """Used to calculate the size of slices"""
        stop, start = index.stop, index.start
        if start is None:
            start = 0
        if stop is None:
            stop = len(self)
        size = stop - start
        if isinstance(size, BitVec):
            size = local_simplify(size)
        else:
            size = BitVecConstant(self.index_size, size)
        if not isinstance(size, BitVecConstant):
            raise ExpressionError("Size could not be simplified to a constant in a slice operation")
        return start, stop, size.value

    def _concatenate(self, array_a: "Array", array_b: "Array") -> "Array":
        """Build a new array from the concatenation of the operands"""
        new_arr = ArrayVariable(
            index_size=self.index_size,
            length=len(array_a) + len(array_b),
            value_size=self.value_size,
            name="concatenation",
        )
        for index in range(len(array_a)):
            new_arr = new_arr.store(index, local_simplify(array_a[index]))
        for index in range(len(array_b)):
            new_arr = new_arr.store(index + len(array_a), local_simplify(array_b[index]))
        return new_arr

    def __add__(self, other):
        return self._concatenate(self, other)

    def __radd__(self, other):
        return self._concatenate(other, self)

    @lru_cache(maxsize=128, typed=True)
    def read_BE(self, address: Union[int, BitVec], size: int) -> Union[BitVec, int]:
        address = self.cast_index(address)
        bytes = []
        for offset in range(size):
            bytes.append(self.cast_value(self[address + offset]))
        return BitVecConcat(operands=tuple(bytes))

    @lru_cache(maxsize=128, typed=True)
    def read_LE(self, address: Union[int, BitVec], size: int) -> Union[BitVec, int]:
        address = self.cast_index(address)
        bytes = []
        for offset in range(size):
            bytes.append(self.cast_value(self[address + offset]))
        return BitVecConcat(operands=tuple(reversed(bytes)))

    def write_BE(
        self, address: Union[int, BitVec], value: Union[int, BitVec], size: int
    ) -> "Array":
        address = self.cast_index(address)
        value = BitVecConstant(size=size * self.value_size, value=0).cast(value)
        array = self
        for offset in range(size):
            array = array.store(
                address + offset,
                BitVecExtract(value, (size - 1 - offset) * self.value_size, self.value_size),
            )
        return array

    def write_LE(
        self, address: Union[int, BitVec], value: Union[int, BitVec], size: int
    ) -> "Array":
        address = self.cast_index(address)
        value = BitVec(size * self.value_size).cast(value)
        array = self
        for offset in reversed(range(size)):
            array = array.store(
                address + offset,
                BitVecExtract(value, (size - 1 - offset) * self.value_size, self.value_size),
            )
        return array


class ArrayConstant(Array, Constant):
    __xslots__: Tuple[str, ...] = ("_index_size", "_value_size")

    def __init__(
        self,
        *,
        index_size: int,
        value_size: int,
        **kwargs,
    ):
        self._index_size = index_size
        self._value_size = value_size
        super().__init__(**kwargs)

    @property
    def index_size(self) -> int:
        return self._index_size

    @property
    def value_size(self) -> int:
        return self._value_size

    @property
    def length(self) -> int:
        return len(self.value)

    def select(self, index):
        """ ArrayConstant get """
        index = self.cast_index(index)
        return self._select(index)

    @lru_cache(maxsize=128, typed=True)
    def _select(self, index):
        """ ArrayConstant get """
        index = self.cast_index(index)
        if isinstance(index, Constant):
            return BitVecConstant(
                size=self.value_size, value=self.value[index.value], taint=self.taint
            )

        # Index being symbolic generates a symbolic result !
        result: BitVec = BitVecConstant(size=self.value_size, value=0, taint=("out_of_bounds"))
        for i, c in enumerate(self.value):
            result = BitVecITE(
                index == i, BitVecConstant(size=self.value_size, value=c), result, taint=self.taint
            )
        return result

    def read(self, offset, size):
        assert len(self.value[offset : offset + size]) == size
        return ArrayConstant(
            index_size=self.index_size,
            value_size=self.value_size,
            value=self.value[offset : offset + size],
        )


class ArrayVariable(Array, Variable):
    """
    An Array expression is a mapping from bitvector of index_size bits
    into bitvectors of value_size bits.

    If a default value is provided reading from an unused index will return the
    default. Otherwise each unused position in the array represents a free bitvector.

    If a length maximum index is provided, accessing over the max is undefined.
    Otherwise the array is unbounded.

    """

    __xslots__: Tuple[str, ...] = (
        "_index_size",
        "_value_size",
        "_length",
        "_default",
    )

    @property
    def length(self):
        return self._length

    def __init__(
        self,
        *,
        index_size: int,
        value_size: int,
        length: Optional[int] = None,
        default: Optional[int] = None,
        **kwargs,
    ):
        """
         This is a mapping from BV to BV. Normally used to represent a memory.

        :param index_size: Number of bits in the addressing side
        :param length: Max address allowed
        :param value_size: Number of bits in tha value side
        :param default: Reading from an uninitialized index will return default
                        if provided. If not the behaivor mimics thtat from smtlib,
                        the returned value is a free symbol.
        :param kwargs: Used in other parent classes
        """
        assert index_size in (32, 64, 256)
        assert value_size in (8, 16, 32, 64, 256)
        assert length is None or 0 <= length < 2 ** index_size
        self._index_size = index_size
        self._length = length
        self._value_size = value_size
        self._default = default
        super().__init__(**kwargs)

    @property
    def index_size(self):
        return self._index_size

    @property
    def value_size(self):
        return self._value_size

    @property
    def default(self):
        return self._default

    @lru_cache(maxsize=128, typed=True)
    def select(self, index):
        """Gets an element from an empty Array."""
        default = self._default
        if default is not None:
            return default
        index = self.cast_index(index)
        return ArraySelect(self, index)

    def store(self, index, value):
        index = self.cast_index(index)
        value = local_simplify(self.cast_value(value))
        return ArrayStore(array=self, index=index, value=value)

    @property
    def written(self):
        return frozenset()

    def is_known(self, index):
        return False

    @property
    def underlying_variable(self):
        array = self
        while not isinstance(array, ArrayVariable):
            array = array.array
        return array


class ArrayOperation(Array, Operation, abstract=True):
    """ It's an operation that results in an Array"""

    pass


def get_items(array):
    if isinstance(array, ArrayStore):
        yield from get_items_array_store(array)
    elif isinstance(array, ArraySlice):
        yield from get_items_array_slice(array)
    elif isinstance(array, ArrayConstant):
        yield from get_items_array_constant(array)
    return


def get_items_array_slice(array):
    assert isinstance(array, ArraySlice)
    for offset, value in get_items(array.array):
        yield offset + array.offset, value


def get_items_array_store(array):
    assert isinstance(array, ArrayStore)
    while isinstance(array, ArrayStore):
        yield array.index, array.value
        array = array.array
    yield from get_items(array)


def get_items_array_constant(array):
    assert isinstance(array, ArrayConstant)
    for index, value in enumerate(array.value):
        yield index, value


def get_items_array_variable(array):
    assert isinstance(array, ArrayVariable)
    raise GeneratorExit


class ArrayStore(ArrayOperation):
    __xslots__: Tuple[str, ...] = (
        "_written#v",
        "_concrete_cache#v",
        "_length#v",
        "_default#v",
    )

    def __init__(self, array: Array, index: BitVec, value: BitVec, **kwargs):
        assert index.size == array.index_size
        assert value.size == array.value_size
        self._written: Optional[Set[Any]] = None  # Cache of the known indexes
        self._concrete_cache: Dict[Any, Any] = dict()
        self._length = array.length
        self._default = array.default

        # recreate and reuse cache
        # if isinstance(index, Constant) and isinstance(array, ArrayStore) and array._concrete_cache is not None:
        #    self._concrete_cache = dict(array._concrete_cache)
        #    self._concrete_cache[index.value] = value

        super().__init__(
            operands=(array, index, value),
            **kwargs,
        )

    @property
    def concrete_cache(self):
        for index, value in get_items(self):
            if not isinstance(index, Constant):
                break
            if index.value not in self._concrete_cache:
                self._concrete_cache[index.value] = value
        return self._concrete_cache

    @property
    def written(self):
        # Calculate only first time
        # This can have repeated and reused written indexes.
        if not self._written:
            self._written = {offset for offset, _ in get_items(self)}
        return self._written

    def is_known(self, index):
        if isinstance(index, Constant) and index.value in self.concrete_cache:
            return BoolConstant(value=True)

        is_known_index: Bool = BoolConstant(value=False)
        written = self.written
        for known_index in written:
            if isinstance(index, Constant) and isinstance(known_index, Constant):
                if known_index.value == index.value:
                    return BoolConstant(value=True)
            is_known_index = BoolOr(is_known_index.cast(index == known_index), is_known_index)
        return is_known_index

    @property
    def length(self):
        return self._length

    @property
    def default(self):
        return self._default

    @property
    def index_size(self):
        return self.index.size

    @property
    def value_size(self):
        return self.value.size

    @property
    def array(self):
        return self.operands[0]

    @property
    def name(self):
        return self.operands[0].name

    @property
    def index(self):
        return self.operands[1]

    @property
    def value(self):
        return self.operands[2]

    def select(self, index):

        """Gets an element from the Array.
        If the element was not previously the default is used.
        """
        index = local_simplify(self.cast_index(index))

        # Emulate list[-1]
        has_length = self.length is not None
        if has_length:
            index = local_simplify(BitVecITE(index < 0, self.length + index, index))

        if isinstance(index, Constant):
            if has_length and index.value >= self.length:
                raise IndexError
            if index.value in self.concrete_cache:
                return self.concrete_cache[index.value]

        default = self.default
        if default is None:
            # No default. Returns normal array select
            return ArraySelect(self, index)

        # if a default is defined we need to check if the index was previously written
        return local_simplify(
            BitVecITE(self.is_known(index), ArraySelect(self, index), self.cast_value(default))
        )

    def store(self, index, value):
        casted = self.cast_index(index)
        index = local_simplify(casted)
        value = self.cast_value(value)
        new_array = ArrayStore(self, index, value)
        return new_array

    def __eq__(self, other):
        return self._compare_buffers(self, self.cast(other))


class ArraySlice(ArrayOperation):
    """Provides a projection of an underlying array.
    Lets you slice an array without copying it.
    (It needs to be simplified out before translating it smtlib)
    """

    def __init__(self, array: "Array", offset: int, size: int, **kwargs):
        if not isinstance(array, Array):
            raise ValueError("Array expected")

        super().__init__(
            operands=(array, array.cast_index(offset), array.cast_index(size)),
            **kwargs,
        )

    @property
    def array(self):
        return self.operands[0]

    @property
    def offset(self):
        return self.operands[1]

    @property
    def length(self):
        return self.operands[2].value

    @property
    def index_size(self):
        return self.array.index_size

    @property
    def value_size(self):
        return self.array.value_size

    @property
    def underlying_variable(self):
        return self.array.underlying_variable

    def select(self, index):
        index = self.cast_index(index)
        if isinstance(index, Constant):
            length = self.length
            if length is not None and index.value >= length:
                raise IndexError
        return self.array.select(local_simplify(index + self.offset))

    def store(self, index, value):
        return ArraySlice(
            self.array.store(index + self.offset, value),
            offset=self.offset,
            size=len(self),
        )

    @property
    def default(self):
        return self.array.default

    def __eq__(self, other):
        # Ignore the taint for eq comparison
        return self._compare_buffers(self, self.cast(other))


class MutableArray:
    """
    Arrayproxy is a layer on top of an array that provides mutability and some
    simple optimizations for concrete indexes.

    It is not hasheable.
    Think:
        bytearray <-> MutableArray  ::: not hasheable, mutable
        bytes <-> Array (ArraySlice, ArrayVariable, ArrayStore) ::: hasheable, notmutable

    """

    def __init__(self, array: Array):
        if isinstance(array, MutableArray):
            array = array._array

        self._array: Array = array

    def __eq__(self, other):
        """ Comparing the inner array of a MutableArray with other"""
        return self.array == other

    def __hash__(self):
        raise NotImplementedError()

    @property
    def underlying_variable(self):
        if isinstance(self._array, ArrayVariable):
            return self._array.underlying_variable
        # NOTE: What to do here?
        assert False
        return self._array

    @property
    def name(self):
        if isinstance(self._array, ArrayVariable):
            return self._array.name
        # NOTE: What to do here?
        assert False
        return None

    @property
    def array(self):
        return self._array

    @property
    def operands(self):
        return (self._array,)

    @property
    def index_size(self):
        return self._array.index_size

    @property
    def length(self):
        return self._array.length

    @property
    def value_size(self):
        return self._array.value_size

    @property
    def taint(self):
        return self._array.taint

    @property
    def default(self):
        return self._array.default

    def __len__(self):
        return len(self._array)

    def select(self, index):
        return self._array.select(index)

    def store(self, index, value):
        self._array = self._array.store(index, value)
        assert self._array is not None
        return self

    @property
    def written(self):
        return self._array.written

    def __getitem__(self, index):
        result = self._array[index]
        if isinstance(index, slice):
            return MutableArray(result)
        return result

    def __setitem__(self, index, value):
        if isinstance(index, slice):
            start, stop, size = self._array._fix_slice(index)
            assert len(value) == size
            for i in range(size):
                self._array = self._array.store(start + i, value[i])
        else:
            self._array = self._array.store(index, value)
        assert self._array is not None
        return self

    def write_BE(self, address, value, size):
        self._array = self._array.write_BE(address, value, size)
        assert self._array is not None
        return self

    def read_BE(self, address, size):
        return self._array.read_BE(address, size)

    def write(self, offset, buf):
        self._array = self._array.write(offset, buf)
        assert self._array is not None

        return self

    def read(self, offset, size):
        return MutableArray(self._array[offset : offset + size])

    def __ne__(self, other):
        return BoolNot(self == other)

    def __add__(self, other):
        if isinstance(other, MutableArray):
            other = other.array
        return MutableArray(self.array + other)

    def __radd__(self, other):
        if isinstance(other, MutableArray):
            other = other.array
        return MutableArray(other + self.array)


class ArraySelect(BitVecOperation):
    __xslots__ = BitVecOperation.__xslots__

    def __init__(self, array: "Array", index: "BitVec", *args, **kwargs):
        assert isinstance(array, Array)
        assert index.size == array.index_size
        super().__init__(size=array.value_size, operands=(array, index), **kwargs)

    @property
    def array(self):
        return self.operands[0]

    @property
    def index(self):
        return self.operands[1]

    def __repr__(self):
        return f"<ArraySelect {self.index} from array {self.array}>"


class BitVecSignExtend(BitVecOperation):
    def __init__(self, operand: BitVec, size: int, *args, **kwargs):
        super().__init__(size=size, operands=(operand,), **kwargs)

    @property
    def extend(self):
        return self.size - self.operands[0].size


class BitVecZeroExtend(BitVecOperation):
    def __init__(self, size: int, operand: BitVec, *args, **kwargs):
        super().__init__(size=size, operands=(operand,), **kwargs)

    @property
    def extend(self):
        return self.size - self.operands[0].size


class BitVecExtract(BitVecOperation):
    __xslots__ = ("_offset",)

    def __init__(self, operand: "BitVec", offset: int, size: int, *args, **kwargs):
        assert offset >= 0 and offset + size <= operand.size
        super().__init__(size=size, operands=(operand,), **kwargs)
        self._offset = offset

    @property
    def value(self):
        return self.operands[0]

    @property
    def begining(self):
        return self._offset

    @property
    def end(self):
        return self.begining + self.size - 1


class BitVecConcat(BitVecOperation):
    def __init__(self, operands: Tuple[BitVec, ...], **kwargs):
        size = sum(x.size for x in operands)
        super().__init__(size=size, operands=operands, **kwargs)


class BitVecITE(BitVecOperation):
    __xslots__ = BitVecOperation.__xslots__

    def __init__(
        self,
        condition: Bool,
        true_value: BitVec,
        false_value: BitVec,
        **kwargs,
    ):

        super().__init__(
            size=true_value.size, operands=(condition, true_value, false_value), **kwargs
        )

    @property
    def condition(self):
        return self.operands[0]

    @property
    def true_value(self):
        return self.operands[1]

    @property
    def false_value(self):
        return self.operands[2]


# auxiliary functions. Maybe move to operators
def issymbolic(value) -> bool:
    """
    Helper to determine whether an object is symbolic (e.g checking
    if data read from memory is symbolic)

    :param object value: object to check
    :return: whether `value` is symbolic
    :rtype: bool
    """
    return isinstance(value, (Expression, MutableArray))


def istainted(arg, taint=None):
    """
    Helper to determine whether an object if tainted.
    :param arg: a value or Expression
    :param taint: a regular expression matching a taint value (eg. 'IMPORTANT.*'). If None, this function checks for any taint value.
    """

    if not issymbolic(arg):
        return False
    if taint is None:
        return len(arg.taint) != 0
    for arg_taint in arg.taint:
        m = re.match(taint, arg_taint, re.DOTALL | re.IGNORECASE)
        if m:
            return True
    return False


def get_taints(arg, taint=None):
    """
    Helper to list an object taints.
    :param arg: a value or Expression
    :param taint: a regular expression matching a taint value (eg. 'IMPORTANT.*'). If None, this function checks for any taint value.
    """

    if not issymbolic(arg):
        return
    for arg_taint in arg.taint:
        if taint is not None:
            m = re.match(taint, arg_taint, re.DOTALL | re.IGNORECASE)
            if m:
                yield arg_taint
        else:
            yield arg_taint
    return


def taint_with(arg, *taints, value_size=256, index_size=256):
    """
    Helper to taint a value.
    :param arg: a value or Expression
    :param taint: a regular expression matching a taint value (eg. 'IMPORTANT.*'). If None, this function checks for any taint value.
    """
    tainted_fset = frozenset(tuple(taints))
    if not issymbolic(arg):
        if isinstance(arg, int):
            arg = BitVecConstant(value_size, arg)
            arg._taint = tainted_fset
        else:
            raise ValueError("type not supported")

    else:
        arg = copy.copy(arg)
        arg._taint |= tainted_fset

    return arg
