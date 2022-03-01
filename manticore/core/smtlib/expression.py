from functools import reduce
from ...exceptions import SmtlibError
import uuid

import re
import copy
from typing import Union, Optional, Dict, Tuple


class ExpressionException(SmtlibError):
    """
    Expression exception
    """

    pass


class ExpressionEvalError(SmtlibError):
    """Exception raised when an expression can't be concretized, typically
    when calling __bool__() fails to produce a True/False boolean result
    """

    pass


class XSlotted(type):
    """
    Metaclass that will propagate slots on multi-inheritance classes
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
            attrs["__slots__"] = attrs["__xslots__"]
        attrs["__hash__"] = object.__hash__
        return super().__new__(cls, clsname, bases, attrs)


class Expression(object, metaclass=XSlotted, abstract=True):
    """Abstract taintable Expression."""

    __xslots__: Tuple[str, ...] = ("_taint",)

    def __init__(self, *, taint: Union[tuple, frozenset] = (), **kwargs):
        if self.__class__ is Expression:
            raise TypeError
        super().__init__()
        self._taint = frozenset(taint)

    def __repr__(self):
        return "<{:s} at {:x}{:s}>".format(type(self).__name__, id(self), self.taint and "-T" or "")

    @property
    def is_tainted(self):
        return len(self._taint) != 0

    @property
    def taint(self):
        return self._taint


def issymbolic(value) -> bool:
    """
    Helper to determine whether an object is symbolic (e.g checking
    if data read from memory is symbolic)

    :param object value: object to check
    :return: whether `value` is symbolic
    :rtype: bool
    """
    return isinstance(value, Expression)


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


def taint_with(arg, *taints, value_bits=256, index_bits=256):
    """
    Helper to taint a value.
    :param arg: a value or Expression
    :param taint: a regular expression matching a taint value (eg. 'IMPORTANT.*'). If None, this function checks for any taint value.
    """

    tainted_fset = frozenset(tuple(taints))
    if not issymbolic(arg):
        if isinstance(arg, int):
            arg = BitVecConstant(size=value_bits, value=arg)
            arg._taint = tainted_fset
        else:
            raise ValueError("type not supported")

    else:
        if isinstance(arg, BitVecVariable):
            arg = arg + BitVecConstant(size=value_bits, value=0, taint=tainted_fset)
        else:
            arg = copy.copy(arg)
            arg._taint |= tainted_fset

    return arg


###############################################################################
# Booleans
class Bool(Expression, abstract=True):
    """Bool expressions represent symbolic value of truth"""

    def __init__(self, *args, **kwargs):
        super().__init__(**kwargs)

    def cast(self, value: Union["Bool", int, bool], **kwargs) -> Union["BoolConstant", "Bool"]:
        if isinstance(value, Bool):
            return value
        return BoolConstant(value=bool(value), **kwargs)

    def __cmp__(self, *args):
        raise NotImplementedError("CMP for Bool")

    def __invert__(self):
        return BoolNot(value=self)

    def __eq__(self, other):
        return BoolEqual(a=self, b=self.cast(other))

    def __hash__(self):
        return object.__hash__(self)

    def __ne__(self, other):
        return BoolNot(value=self == self.cast(other))

    def __and__(self, other):
        return BoolAnd(a=self, b=self.cast(other))

    def __or__(self, other):
        return BoolOr(a=self, b=self.cast(other))

    def __xor__(self, other):
        return BoolXor(a=self, b=self.cast(other))

    def __rand__(self, other):
        return BoolAnd(a=self.cast(other), b=self)

    def __ror__(self, other):
        return BoolOr(a=self.cast(other), b=self)

    def __rxor__(self, other):
        return BoolXor(a=self.cast(other), b=self)

    def __bool__(self):
        # try to be forgiving. Allow user to use Bool in an IF sometimes
        from .visitors import simplify

        x = simplify(self)
        if isinstance(x, Constant):
            return x.value
        raise ExpressionEvalError("__bool__ for Bool")


class BoolVariable(Bool):
    __xslots__: Tuple[str, ...] = ("_name",)

    def __init__(self, *, name: str, **kwargs):
        assert " " not in name
        super().__init__(**kwargs)
        self._name = name

    @property
    def name(self):
        return self._name

    def __copy__(self, memo=""):
        raise ExpressionException("Copying of Variables is not allowed.")

    def __deepcopy__(self, memo=""):
        raise ExpressionException("Copying of Variables is not allowed.")

    def __repr__(self):
        return "<{:s}({:s}) at {:x}>".format(type(self).__name__, self.name, id(self))

    @property
    def declaration(self):
        return f"(declare-fun {self.name} () Bool)"


class BoolConstant(Bool):
    __xslots__: Tuple[str, ...] = ("_value",)

    def __init__(self, *, value: bool, **kwargs):
        super().__init__(**kwargs)
        self._value = value

    def __bool__(self):
        return self.value

    @property
    def value(self):
        return self._value


class BoolOperation(Bool, abstract=True):
    """An operation that results in a Bool"""

    __xslots__: Tuple[str, ...] = ("_operands",)

    def __init__(self, *, operands: Tuple, **kwargs):
        self._operands = operands

        # If taint was not forced by a keyword argument, calculate default
        kwargs.setdefault("taint", reduce(lambda x, y: x.union(y.taint), operands, frozenset()))

        super().__init__(**kwargs)

    @property
    def operands(self):
        return self._operands


class BoolNot(BoolOperation):
    def __init__(self, *, value, **kwargs):
        super().__init__(operands=(value,), **kwargs)


class BoolAnd(BoolOperation):
    def __init__(self, *, a, b, **kwargs):
        super().__init__(operands=(a, b), **kwargs)


class BoolOr(BoolOperation):
    def __init__(self, *, a: "Bool", b: "Bool", **kwargs):
        super().__init__(operands=(a, b), **kwargs)


class BoolXor(BoolOperation):
    def __init__(self, *, a, b, **kwargs):
        super().__init__(operands=(a, b), **kwargs)


class BoolITE(BoolOperation):
    def __init__(self, *, cond: "Bool", true: "Bool", false: "Bool", **kwargs):
        super().__init__(operands=(cond, true, false), **kwargs)


class BitVec(Expression, abstract=True):
    """BitVector expressions have a fixed bit size"""

    __xslots__: Tuple[str, ...] = ("size",)

    def __init__(self, *, size, **kwargs):
        super().__init__(**kwargs)
        self.size = size

    @property
    def mask(self):
        return (1 << self.size) - 1

    @property
    def signmask(self):
        return 1 << (self.size - 1)

    def cast(
        self, value: Union["BitVec", str, int, bytes], **kwargs
    ) -> Union["BitVecConstant", "BitVec"]:
        if isinstance(value, BitVec):
            assert value.size == self.size
            return value
        if isinstance(value, (str, bytes)) and len(value) == 1:
            value = ord(value)
        # Try to support not Integral types that can be casted to int
        if not isinstance(value, int):
            value = int(value)
        # FIXME? Assert it fits in the representation
        return BitVecConstant(size=self.size, value=value, **kwargs)

    def __add__(self, other):
        return BitVecAdd(a=self, b=self.cast(other))

    def __sub__(self, other):
        return BitVecSub(a=self, b=self.cast(other))

    def __mul__(self, other):
        return BitVecMul(a=self, b=self.cast(other))

    def __mod__(self, other):
        return BitVecMod(a=self, b=self.cast(other))

    # object.__divmod__(self, other)
    # object.__pow__(self, other[, modulo])

    def __lshift__(self, other):
        return BitVecShiftLeft(a=self, b=self.cast(other))

    def __rshift__(self, other):
        return BitVecShiftRight(a=self, b=self.cast(other))

    def __and__(self, other):
        return BitVecAnd(a=self, b=self.cast(other))

    def __xor__(self, other):
        return BitVecXor(a=self, b=self.cast(other))

    def __or__(self, other):
        return BitVecOr(a=self, b=self.cast(other))

    # The division operator (/) is implemented by these methods. The
    # __truediv__() method is used when __future__.division is in effect,
    # otherwise __div__() is used. If only one of these two methods is
    # defined, the object will not support division in the alternate context;
    # TypeError will be raised instead.

    def __div__(self, other):
        return BitVecDiv(a=self, b=self.cast(other))

    def __truediv__(self, other):
        return BitVecDiv(a=self, b=self.cast(other))

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
        return BitVecAdd(a=self.cast(other), b=self)

    def __rsub__(self, other):
        return BitVecSub(a=self.cast(other), b=self)

    def __rmul__(self, other):
        return BitVecMul(a=self.cast(other), b=self)

    def __rmod__(self, other):
        return BitVecMod(a=self.cast(other), b=self)

    def __rtruediv__(self, other):
        return BitVecDiv(a=self.cast(other), b=self)

    def __rdiv__(self, other):
        return BitVecDiv(a=self.cast(other), b=self)

    # object.__rdivmod__(self, other)
    # object.__rpow__(self, other)

    def __rlshift__(self, other):
        return BitVecShiftLeft(a=self.cast(other), b=self)

    def __rrshift__(self, other):
        return BitVecShiftRight(a=self.cast(other), b=self)

    def __rand__(self, other):
        return BitVecAnd(a=self.cast(other), b=self)

    def __rxor__(self, other):
        return BitVecXor(a=self.cast(other), b=self)

    def __ror__(self, other):
        return BitVecOr(a=self.cast(other), b=self)

    def __invert__(self):
        return BitVecXor(a=self, b=self.cast(self.mask))

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
        return LessThan(a=self, b=self.cast(other))

    def __le__(self, other):
        return LessOrEqual(a=self, b=self.cast(other))

    def __eq__(self, other):
        return BoolEqual(a=self, b=self.cast(other))

    def __hash__(self):
        return object.__hash__(self)

    def __ne__(self, other):
        return BoolNot(value=BoolEqual(a=self, b=self.cast(other)))

    def __gt__(self, other):
        return GreaterThan(a=self, b=self.cast(other))

    def __ge__(self, other):
        return GreaterOrEqual(a=self, b=self.cast(other))

    def __neg__(self):
        return BitVecNeg(a=self)

    # Unsigned comparisons
    def ugt(self, other):
        return UnsignedGreaterThan(a=self, b=self.cast(other))

    def uge(self, other):
        return UnsignedGreaterOrEqual(a=self, b=self.cast(other))

    def ult(self, other):
        return UnsignedLessThan(a=self, b=self.cast(other))

    def ule(self, other):
        return UnsignedLessOrEqual(a=self, b=self.cast(other))

    def udiv(self, other):
        return BitVecUnsignedDiv(a=self, b=self.cast(other))

    def rudiv(self, other):
        return BitVecUnsignedDiv(a=self.cast(other), b=self)

    def sdiv(self, other):
        return BitVecDiv(a=self, b=self.cast(other))

    def rsdiv(self, other):
        return BitVecDiv(a=self.cast(other), b=self)

    def srem(self, other):
        return BitVecRem(a=self, b=self.cast(other))

    def rsrem(self, other):
        return BitVecRem(a=self.cast(other), b=self)

    def urem(self, other):
        return BitVecUnsignedRem(a=self, b=self.cast(other))

    def rurem(self, other):
        return BitVecUnsignedRem(a=self.cast(other), b=self)

    def sar(self, other):
        return BitVecArithmeticShiftRight(a=self, b=self.cast(other))

    def sal(self, other):
        return BitVecArithmeticShiftLeft(a=self, b=self.cast(other))

    def Bool(self):
        return self != 0


class BitVecVariable(BitVec):
    __xslots__: Tuple[str, ...] = ("_name",)

    def __init__(self, *, size: int, name: str, **kwargs):
        assert " " not in name
        super().__init__(size=size, **kwargs)
        self._name = name

    @property
    def name(self):
        return self._name

    def __copy__(self, memo=""):
        raise ExpressionException("Copying of Variables is not allowed.")

    def __deepcopy__(self, memo=""):
        raise ExpressionException("Copying of Variables is not allowed.")

    def __repr__(self):
        return "<{:s}({:s}) at {:x}>".format(type(self).__name__, self.name, id(self))

    @property
    def declaration(self):
        return f"(declare-fun {self.name} () (_ BitVec {self.size}))"


class BitVecConstant(BitVec):
    __xslots__: Tuple[str, ...] = ("_value",)

    def __init__(self, *, size: int, value: int, **kwargs):
        MASK = (1 << size) - 1
        self._value = value & MASK
        super().__init__(size=size, **kwargs)

    def __bool__(self):
        return self.value != 0

    def __eq__(self, other):
        if self.taint:
            return super().__eq__(other)
        return self.value == other

    def __hash__(self):
        return super().__hash__()

    @property
    def value(self):
        return self._value

    @property
    def signed_value(self):
        if self._value & self.signmask:
            return self._value - (1 << self.size)
        else:
            return self._value


class BitVecOperation(BitVec, abstract=True):
    """An operation that results in a BitVec"""

    __xslots__: Tuple[str, ...] = ("_operands",)

    def __init__(self, *, size, operands: Tuple, **kwargs):
        self._operands = operands

        # If taint was not forced by a keyword argument, calculate default
        kwargs.setdefault("taint", reduce(lambda x, y: x.union(y.taint), operands, frozenset()))

        super().__init__(size=size, **kwargs)

    @property
    def operands(self):
        return self._operands


class BitVecAdd(BitVecOperation):
    def __init__(self, *, a, b, **kwargs):
        super().__init__(size=a.size, operands=(a, b), **kwargs)


class BitVecSub(BitVecOperation):
    def __init__(self, *, a, b, **kwargs):
        super().__init__(size=a.size, operands=(a, b), **kwargs)


class BitVecMul(BitVecOperation):
    def __init__(self, *, a, b, **kwargs):
        super().__init__(size=a.size, operands=(a, b), **kwargs)


class BitVecDiv(BitVecOperation):
    def __init__(self, *, a, b, **kwargs):
        super().__init__(size=a.size, operands=(a, b), **kwargs)


class BitVecUnsignedDiv(BitVecOperation):
    def __init__(self, *, a, b, **kwargs):
        super().__init__(size=a.size, operands=(a, b), **kwargs)


class BitVecMod(BitVecOperation):
    def __init__(self, *, a, b, **kwargs):
        super().__init__(size=a.size, operands=(a, b), **kwargs)


class BitVecRem(BitVecOperation):
    def __init__(self, *, a, b, **kwargs):
        super().__init__(size=a.size, operands=(a, b), **kwargs)


class BitVecUnsignedRem(BitVecOperation):
    def __init__(self, *, a, b, **kwargs):
        super().__init__(size=a.size, operands=(a, b), **kwargs)


class BitVecShiftLeft(BitVecOperation):
    def __init__(self, *, a, b, **kwargs):
        super().__init__(size=a.size, operands=(a, b), **kwargs)


class BitVecShiftRight(BitVecOperation):
    def __init__(self, *, a, b, **kwargs):
        super().__init__(size=a.size, operands=(a, b), **kwargs)


class BitVecArithmeticShiftLeft(BitVecOperation):
    def __init__(self, *, a, b, **kwargs):
        super().__init__(size=a.size, operands=(a, b), **kwargs)


class BitVecArithmeticShiftRight(BitVecOperation):
    def __init__(self, *, a, b, **kwargs):
        super().__init__(size=a.size, operands=(a, b), **kwargs)


class BitVecAnd(BitVecOperation):
    def __init__(self, *, a, b, **kwargs):
        super().__init__(size=a.size, operands=(a, b), **kwargs)


class BitVecOr(BitVecOperation):
    def __init__(self, *, a: BitVec, b: BitVec, **kwargs):
        assert a.size == b.size
        super().__init__(size=a.size, operands=(a, b), **kwargs)


class BitVecXor(BitVecOperation):
    def __init__(self, *, a, b, **kwargs):
        super().__init__(size=a.size, operands=(a, b), **kwargs)


class BitVecNot(BitVecOperation):
    def __init__(self, *, a, **kwargs):
        super().__init__(size=a.size, operands=(a,), **kwargs)


class BitVecNeg(BitVecOperation):
    def __init__(self, *, a, **kwargs):
        super().__init__(size=a.size, operands=(a,), **kwargs)


# Comparing two bitvectors results in a Bool
class LessThan(BoolOperation):
    def __init__(self, *, a, b, **kwargs):
        super().__init__(operands=(a, b), **kwargs)


class LessOrEqual(BoolOperation):
    def __init__(self, *, a, b, **kwargs):
        super().__init__(operands=(a, b), **kwargs)


class BoolEqual(BoolOperation):
    def __init__(self, *, a, b, **kwargs):
        if isinstance(a, BitVec) or isinstance(b, BitVec):
            assert a.size == b.size
        super().__init__(operands=(a, b), **kwargs)


class GreaterThan(BoolOperation):
    def __init__(self, *, a, b, **kwargs):
        assert a.size == b.size
        super().__init__(operands=(a, b), **kwargs)


class GreaterOrEqual(BoolOperation):
    def __init__(self, *, a, b, **kwargs):
        assert a.size == b.size
        super().__init__(operands=(a, b), **kwargs)


class UnsignedLessThan(BoolOperation):
    def __init__(self, *, a, b, **kwargs):
        assert a.size == b.size
        super().__init__(operands=(a, b), **kwargs)


class UnsignedLessOrEqual(BoolOperation):
    def __init__(self, *, a, b, **kwargs):
        assert a.size == b.size
        super().__init__(operands=(a, b), **kwargs)


class UnsignedGreaterThan(BoolOperation):
    def __init__(self, *, a, b, **kwargs):
        assert a.size == b.size
        super().__init__(operands=(a, b), **kwargs)


class UnsignedGreaterOrEqual(BoolOperation):
    def __init__(self, *, a, b, **kwargs):
        assert a.size == b.size
        super(UnsignedGreaterOrEqual, self).__init__(operands=(a, b), **kwargs)


###############################################################################
# Array  BV32 -> BV8  or BV64 -> BV8
class Array(Expression, abstract=True):
    """An Array expression is an unmutable mapping from bitvector to bitvector

    array.index_bits is the number of bits used for addressing a value
    array.value_bits is the number of bits used in the values
    array.index_max counts the valid indexes starting at 0. Accessing outside the bound is undefined
    """

    __xslots__: Tuple[str, ...] = ("_index_bits", "_index_max", "_value_bits")

    def __init__(self, *, index_bits: int, index_max: Optional[int], value_bits: int, **kwargs):
        assert index_bits in (32, 64, 256)
        assert value_bits in (8, 16, 32, 64, 256)
        assert index_max is None or index_max >= 0 and index_max < 2**index_bits
        self._index_bits = index_bits
        self._index_max = index_max
        self._value_bits = value_bits
        super().__init__(**kwargs)
        assert type(self) is not Array, "Abstract class"

    def _get_size(self, index):
        start, stop = self._fix_index(index)
        size = stop - start
        if isinstance(size, BitVec):
            from .visitors import simplify

            size = simplify(size)
        else:
            size = BitVecConstant(size=self.index_bits, value=size)
        assert isinstance(size, BitVecConstant)
        return size.value

    def _fix_index(self, index):
        """
        :param slice index:
        """
        stop, start = index.stop, index.start
        if start is None:
            start = 0
        if stop is None:
            stop = len(self)
        return start, stop

    def cast(self, possible_array):
        if isinstance(possible_array, bytearray):
            # FIXME This should be related to a constrainSet
            arr = ArrayVariable(
                index_bits=self.index_bits,
                index_max=len(possible_array),
                value_bits=8,
                name="cast{}".format(uuid.uuid1()),
            )
            for pos, byte in enumerate(possible_array):
                arr = arr.store(pos, byte)
            return arr
        raise ValueError  # cast not implemented

    def cast_index(self, index: Union[int, "BitVec"]) -> Union["BitVecConstant", "BitVec"]:
        if isinstance(index, int):
            # assert self.index_max is None or index >= 0 and index < self.index_max
            return BitVecConstant(size=self.index_bits, value=index)
        assert index.size == self.index_bits
        return index

    def cast_value(
        self, value: Union["BitVec", str, bytes, int]
    ) -> Union["BitVecConstant", "BitVec"]:
        if isinstance(value, BitVec):
            assert value.size == self.value_bits
            return value
        if isinstance(value, (str, bytes)) and len(value) == 1:
            value = ord(value)
        if not isinstance(value, int):
            value = int(value)
        return BitVecConstant(size=self.value_bits, value=value)

    def __len__(self):
        if self.index_max is None:
            raise ExpressionException("Array max index not set")
        return self.index_max

    @property
    def index_bits(self):
        return self._index_bits

    @property
    def value_bits(self):
        return self._value_bits

    @property
    def index_max(self):
        return self._index_max

    def select(self, index):
        index = self.cast_index(index)
        return ArraySelect(array=self, index=index)

    def store(self, index, value):
        return ArrayStore(array=self, index=self.cast_index(index), value=self.cast_value(value))

    def write(self, offset, buf):
        if not isinstance(buf, (Array, bytearray)):
            raise TypeError(f"Array or bytearray expected got {type(buf)}")
        arr = self
        for i, val in enumerate(buf):
            arr = arr.store(offset + i, val)
        return arr

    def read(self, offset, size):
        return ArraySlice(array=self, offset=offset, size=size)

    def __getitem__(self, index):
        if isinstance(index, slice):
            start, stop = self._fix_index(index)
            size = self._get_size(index)
            return ArraySlice(array=self, offset=start, size=size)
        else:
            if self.index_max is not None:
                if not isinstance(index, Expression) and index >= self.index_max:
                    raise IndexError
        return self.select(self.cast_index(index))

    def __iter__(self):
        for i in range(len(self)):
            yield self[i]

    def __eq__(self, other):
        # FIXME taint
        def compare_buffers(a, b):
            if len(a) != len(b):
                return BoolConstant(value=False)
            cond = BoolConstant(value=True)
            for i in range(len(a)):
                cond = BoolAnd(a=cond.cast(a[i] == b[i]), b=cond)
                if cond is BoolConstant(value=False):
                    return BoolConstant(value=False)
            return cond

        return compare_buffers(self, other)

    def __ne__(self, other):
        return BoolNot(value=self == other)

    def __hash__(self):
        return super().__hash__()

    @property
    def underlying_variable(self):
        array = self
        while not isinstance(array, ArrayVariable):
            array = array.array
        return array

    def read_BE(self, address, size):
        address = self.cast_index(address)
        bytes = []
        for offset in range(size):
            bytes.append(self.get(address + offset, 0))
        return BitVecConcat(size_dest=size * self.value_bits, operands=tuple(bytes))

    def read_LE(self, address, size):
        address = self.cast_index(address)
        bytes = []
        for offset in range(size):
            bytes.append(self.get(address + offset, 0))
        return BitVecConcat(size_dest=size * self.value_bits, operands=tuple(reversed(bytes)))

    def write_BE(self, address, value, size):
        address = self.cast_index(address)
        value = BitVecConstant(size=size * self.value_bits, value=0).cast(value)
        array = self
        for offset in range(size):
            array = array.store(
                address + offset,
                BitVecExtract(
                    operand=value,
                    offset=(size - 1 - offset) * self.value_bits,
                    size=self.value_bits,
                ),
            )
        return array

    def write_LE(self, address, value, size):
        address = self.cast_index(address)
        value = BitVecConstant(size=size * self.value_bits, value=0).cast(value)
        array = self
        for offset in reversed(range(size)):
            array = array.store(
                address + offset,
                BitVecExtract(
                    operand=value,
                    offset=(size - 1 - offset) * self.value_bits,
                    size=self.value_bits,
                ),
            )
        return array

    def __add__(self, other):
        if not isinstance(other, (Array, bytearray)):
            raise TypeError("can't concat Array to {}".format(type(other)))
        if isinstance(other, Array):
            if self.index_bits != other.index_bits or self.value_bits != other.value_bits:
                raise ValueError("Array sizes do not match for concatenation")

        from .visitors import simplify

        # FIXME This should be related to a constrainSet
        new_arr = ArrayProxy(
            array=ArrayVariable(
                index_bits=self.index_bits,
                index_max=self.index_max + len(other),
                value_bits=self.value_bits,
                name="concatenation{}".format(uuid.uuid1()),
            )
        )
        for index in range(self.index_max):
            new_arr[index] = simplify(self[index])
        for index in range(len(other)):
            new_arr[index + self.index_max] = simplify(other[index])
        return new_arr

    def __radd__(self, other):
        if not isinstance(other, (Array, bytearray, bytes)):
            raise TypeError("can't concat Array to {}".format(type(other)))
        if isinstance(other, Array):
            if self.index_bits != other.index_bits or self.value_bits != other.value_bits:
                raise ValueError("Array sizes do not match for concatenation")

        from .visitors import simplify

        # FIXME This should be related to a constrainSet
        new_arr = ArrayProxy(
            array=ArrayVariable(
                index_bits=self.index_bits,
                index_max=self.index_max + len(other),
                value_bits=self.value_bits,
                name="concatenation{}".format(uuid.uuid1()),
            )
        )
        for index in range(len(other)):
            new_arr[index] = simplify(other[index])
        _concrete_cache = new_arr._concrete_cache
        for index in range(self.index_max):
            new_arr[index + len(other)] = simplify(self[index])
        new_arr._concrete_cache.update(_concrete_cache)
        return new_arr


class ArrayVariable(Array):
    __xslots__: Tuple[str, ...] = ("_name",)

    def __init__(self, *, index_bits, index_max, value_bits, name, **kwargs):
        assert " " not in name
        super().__init__(
            index_bits=index_bits, index_max=index_max, value_bits=value_bits, **kwargs
        )
        self._name = name

    @property
    def name(self):
        return self._name

    def __copy__(self, memo=""):
        raise ExpressionException("Copying of Variables is not allowed.")

    def __deepcopy__(self, memo=""):
        raise ExpressionException("Copying of Variables is not allowed.")

    def __repr__(self):
        return "<{:s}({:s}) at {:x}>".format(type(self).__name__, self.name, id(self))

    @property
    def declaration(self):
        return f"(declare-fun {self.name} () (Array (_ BitVec {self.index_bits}) (_ BitVec {self.value_bits})))"


class ArrayOperation(Array):
    """An operation that result in an Array"""

    __xslots__: Tuple[str, ...] = ("_operands",)

    def __init__(self, *, array: Array, operands: Tuple, **kwargs):
        self._operands = (array, *operands)

        # If taint was not forced by a keyword argument, calculate default
        kwargs.setdefault("taint", reduce(lambda x, y: x.union(y.taint), operands, frozenset()))

        super().__init__(
            index_bits=array.index_bits,
            index_max=array.index_max,
            value_bits=array.value_bits,
            **kwargs,
        )

    @property
    def operands(self):
        return self._operands


class ArrayStore(ArrayOperation):
    def __init__(self, *, array: "Array", index: "BitVec", value: "BitVec", **kwargs):
        assert index.size == array.index_bits
        assert value.size == array.value_bits
        super().__init__(array=array, operands=(index, value), **kwargs)

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

    def __getstate__(self):
        state = {}
        array = self
        items = []
        while isinstance(array, ArrayStore):
            items.append((array.index, array.value))
            array = array.array
        state["_array"] = array
        state["_items"] = items
        state["_taint"] = self.taint
        return state

    def __setstate__(self, state):
        array = state["_array"]
        for index, value in reversed(state["_items"][0:]):
            array = array.store(index, value)
        self._index_bits = array.index_bits
        self._index_max = array.index_max
        self._value_bits = array.value_bits
        self._taint = state["_taint"]
        index, value = state["_items"][0]
        self._operands = (array, index, value)


class ArraySlice(ArrayOperation):
    __xslots__: Tuple[str, ...] = ("_slice_offset", "_slice_size")

    def __init__(self, *, array: Union["Array", "ArrayProxy"], offset: int, size: int, **kwargs):
        if not isinstance(array, Array):
            raise ValueError("Array expected")
        if isinstance(array, ArrayProxy):
            array = array._array
        self._operands = (array,)
        super().__init__(
            array=array, operands=(self.cast_index(offset), self.cast_index(size)), **kwargs
        )

        self._slice_offset = offset
        self._slice_size = size

    @property
    def array(self):
        return self._operands[0]

    @property
    def underlying_variable(self):
        return self.array.underlying_variable

    @property
    def index_bits(self):
        return self.array.index_bits

    @property
    def index_max(self):
        return self._slice_size

    @property
    def value_bits(self):
        return self.array.value_bits

    def select(self, index):
        return self.array.select(index + self._slice_offset)

    def store(self, index, value):
        return ArraySlice(
            array=self.array.store(index + self._slice_offset, value),
            offset=self._slice_offset,
            size=self._slice_size,
        )


class ArrayProxy(Array):
    __xslots__: Tuple[str, ...] = (
        "constraints",
        "_default",
        "_concrete_cache",
        "_written",
        "_array",
        "_name",
    )

    def __init__(self, *, array: Array, default: Optional[int] = None, **kwargs):
        self._default = default
        self._concrete_cache: Dict[int, int] = {}
        self._written = None
        if isinstance(array, ArrayProxy):
            # copy constructor
            super().__init__(
                index_bits=array.index_bits,
                index_max=array.index_max,
                value_bits=array.value_bits,
                **kwargs,
            )
            self._array: Array = array._array
            self._name: str = array._name
            if default is None:
                self._default = array._default
            self._concrete_cache = dict(array._concrete_cache)
            self._written = set(array.written)
        elif isinstance(array, ArrayVariable):
            # fresh array proxy
            super().__init__(
                index_bits=array.index_bits,
                index_max=array.index_max,
                value_bits=array.value_bits,
                **kwargs,
            )
            self._array = array
            self._name = array.name
        else:
            # arrayproxy for a prepopulated array
            super().__init__(
                index_bits=array.index_bits,
                index_max=array.index_max,
                value_bits=array.value_bits,
                **kwargs,
            )
            self._name = array.underlying_variable.name
            self._array = array

    @property
    def underlying_variable(self):
        return self._array.underlying_variable

    @property
    def array(self):
        return self._array

    @property
    def name(self):
        return self._name

    @property
    def operands(self):
        return (self._array,)

    @property
    def index_bits(self):
        return self._array.index_bits

    @property
    def index_max(self):
        return self._array.index_max

    @property
    def value_bits(self):
        return self._array.value_bits

    @property
    def taint(self):
        return self._array.taint

    def select(self, index):
        return self.get(index)

    def store(self, index, value):
        if not isinstance(index, Expression):
            index = self.cast_index(index)
        if not isinstance(value, Expression):
            value = self.cast_value(value)
        from .visitors import simplify

        index = simplify(index)
        if isinstance(index, Constant):
            self._concrete_cache[index.value] = value
        else:
            # delete all cache as we do not know what this may overwrite.
            self._concrete_cache = {}

        # potentially generate and update .written set
        # if index is symbolic it may overwrite other previous indexes
        self.written.add(index)
        self._array = self._array.store(index, value)
        return self

    def __getitem__(self, index):
        if isinstance(index, slice):
            start, stop = self._fix_index(index)
            size = self._get_size(index)
            array_proxy_slice = ArrayProxy(
                array=ArraySlice(array=self, offset=start, size=size), default=self._default
            )
            array_proxy_slice._concrete_cache = {}
            for k, v in self._concrete_cache.items():
                if k >= start and k < start + size:
                    array_proxy_slice._concrete_cache[k - start] = v

            for i in self.written:
                array_proxy_slice.written.add(i - start)
            return array_proxy_slice
        else:
            if self.index_max is not None:
                if not isinstance(index, Expression) and index >= self.index_max:
                    raise IndexError
            return self.get(index, self._default)

    def __setitem__(self, index, value):
        if isinstance(index, slice):
            start, stop = self._fix_index(index)
            size = self._get_size(index)
            assert len(value) == size
            for i in range(size):
                self.store(start + i, value[i])
        else:
            self.store(index, value)

    def __getstate__(self):
        state = {}
        state["_default"] = self._default
        state["_array"] = self._array
        state["name"] = self.name
        state["_concrete_cache"] = self._concrete_cache
        return state

    def __setstate__(self, state):
        self._default = state["_default"]
        self._array = state["_array"]
        self._name = state["name"]
        self._concrete_cache = state["_concrete_cache"]
        self._written = None

    def __copy__(self):
        return ArrayProxy(array=self)

    @property
    def written(self):
        # Calculate only first time
        if self._written is None:
            written = set()
            # take out Proxy sleve
            array = self._array
            offset = 0
            while not isinstance(array, ArrayVariable):
                if isinstance(array, ArraySlice):
                    # if it is a proxy over a slice take out the slice too
                    offset += array._slice_offset
                else:
                    # The index written to underlaying Array are displaced when sliced
                    written.add(array.index - offset)
                array = array.array
            assert isinstance(array, ArrayVariable)
            self._written = written
        return self._written

    def is_known(self, index):
        if isinstance(index, Constant) and index.value in self._concrete_cache:
            return BoolConstant(value=True)

        is_known_index = BoolConstant(value=False)
        written = self.written
        if isinstance(index, Constant):
            for i in written:
                # check if the concrete index is explicitly in written
                if isinstance(i, Constant) and index.value == i.value:
                    return BoolConstant(value=True)

                # Build an expression to check if our concrete index could be the
                # solution for anyof the used symbolic indexes
                is_known_index = BoolOr(a=is_known_index.cast(index == i), b=is_known_index)
            return is_known_index

        # The index is symbolic we need to compare it agains it all
        for known_index in written:
            is_known_index = BoolOr(a=is_known_index.cast(index == known_index), b=is_known_index)

        return is_known_index

    def get(self, index, default=None):
        if default is None:
            default = self._default
        index = self.cast_index(index)

        if self.index_max is not None:
            from .visitors import simplify

            index = simplify(
                BitVecITE(
                    size=self.index_bits,
                    condition=index < 0,
                    true_value=self.index_max + index + 1,
                    false_value=index,
                )
            )
        if isinstance(index, Constant) and index.value in self._concrete_cache:
            return self._concrete_cache[index.value]

        if default is not None:
            default = self.cast_value(default)
            is_known = self.is_known(index)
            if isinstance(is_known, Constant) and is_known.value == False:
                return default
        else:
            return self._array.select(index)

        value = self._array.select(index)
        return BitVecITE(
            size=self._array.value_bits, condition=is_known, true_value=value, false_value=default
        )


class ArraySelect(BitVec):
    __xslots__: Tuple[str, ...] = ("_operands",)

    def __init__(self, *, array: "Array", index: "BitVec", **kwargs):
        assert isinstance(array, Array)
        assert index.size == array.index_bits
        self._operands = (array, index)

        # If taint was not forced by a keyword argument, calculate default
        kwargs.setdefault("taint", frozenset({y for x in self._operands for y in x.taint}))

        super().__init__(size=array.value_bits, **kwargs)

    @property
    def array(self):
        return self._operands[0]

    @property
    def index(self):
        return self._operands[1]

    @property
    def operands(self):
        return self._operands

    def __repr__(self):
        return f"<ArraySelect obj with index={self.index}:\n{self.array}>"


class BitVecSignExtend(BitVecOperation):
    __xslots__: Tuple[str, ...] = ("extend",)

    def __init__(self, *, operand: "BitVec", size_dest: int, **kwargs):
        assert size_dest >= operand.size
        super().__init__(size=size_dest, operands=(operand,), **kwargs)
        self.extend = size_dest - operand.size


class BitVecZeroExtend(BitVecOperation):
    __xslots__: Tuple[str, ...] = ("extend",)

    def __init__(self, *, size_dest: int, operand: "BitVec", **kwargs):
        assert size_dest >= operand.size
        super().__init__(size=size_dest, operands=(operand,), **kwargs)
        self.extend = size_dest - operand.size


class BitVecExtract(BitVecOperation):
    __xslots__: Tuple[str, ...] = ("_begining", "_end")

    def __init__(self, *, operand: "BitVec", offset: int, size: int, **kwargs):
        assert offset >= 0 and offset + size <= operand.size
        super().__init__(size=size, operands=(operand,), **kwargs)
        self._begining = offset
        self._end = offset + size - 1

    @property
    def value(self):
        return self.operands[0]

    @property
    def begining(self):
        return self._begining

    @property
    def end(self):
        return self._end


class BitVecConcat(BitVecOperation):
    def __init__(self, *, size_dest: int, operands: Tuple, **kwargs):
        assert all(isinstance(x, BitVec) for x in operands)
        assert size_dest == sum(x.size for x in operands)
        super().__init__(size=size_dest, operands=operands, **kwargs)


class BitVecITE(BitVecOperation):
    def __init__(
        self,
        *,
        size: int,
        condition: Union["Bool", bool],
        true_value: "BitVec",
        false_value: "BitVec",
        **kwargs,
    ):
        assert true_value.size == size
        assert false_value.size == size
        super().__init__(size=size, operands=(condition, true_value, false_value), **kwargs)

    @property
    def condition(self):
        return self.operands[0]

    @property
    def true_value(self):
        return self.operands[1]

    @property
    def false_value(self):
        return self.operands[2]


Constant = (BitVecConstant, BoolConstant)
Variable = (BitVecVariable, BoolVariable, ArrayVariable)
Operation = (BitVecOperation, BoolOperation, ArrayOperation, ArraySelect)
