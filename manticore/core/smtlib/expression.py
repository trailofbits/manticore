from functools import reduce
from ...exceptions import SmtlibError
import uuid

import re
import copy
from typing import Union, Optional, Dict, Tuple, List


class ExpressionException(SmtlibError):
    """
    Expression exception
    """

    pass


class Expression(object):
    """ Abstract taintable Expression. """

    __slots__: Tuple[str, ...] = ()
    __xslots__: Tuple[str, ...] = ("_taint",)

    def __init__(self, taint: Union[tuple, frozenset] = (), **kwargs):
        assert not kwargs
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
    return isinstance(value, (Expression, ArrayProxy))


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
            arg = BitVecConstant(value_bits, arg)
            arg._taint = tainted_fset
        else:
            raise ValueError("type not supported")

    else:
        arg = copy.copy(arg)
        arg._taint |= tainted_fset

    return arg


class Variable(Expression):
    __slots__ = ()
    __xslots__: Tuple[str, ...] = ("_name",)

    def __init__(self, name: str, **kwargs):
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
    __slots__ = ()
    __xslots__: Tuple[str, ...] = ("_value",)

    def __init__(self, value: Union[bool, int], **kwargs):
        super().__init__(**kwargs)
        self._value = value

    @property
    def value(self):
        return self._value


class Operation(Expression):
    __slots__ = ()
    __xslots__: Tuple[str, ...] = ("_operands",)

    def __init__(self, operands: Tuple[Expression, ...], taint=None, **kwargs):
        # assert len(operands) > 0
        # assert all(isinstance(x, Expression) for x in operands)
        self._operands = operands

        # If taint was not forced by a keyword argument, calculate default
        if taint is None:
            taint = reduce(lambda x, y: x.union(y.taint), operands, frozenset())

        super().__init__(taint=taint, **kwargs)

    @property
    def operands(self):
        return self._operands


###############################################################################
# Booleans
class Bool(Expression):
    __slots__: Tuple[str, ...] = tuple()

    def cast(self, value: Union["Bool", int, bool], **kwargs) -> Union["BoolConstant", "Bool"]:
        if isinstance(value, Bool):
            return value
        return BoolConstant(bool(value), **kwargs)

    def __cmp__(self, *args):
        raise NotImplementedError("CMP for Bool")

    def __invert__(self):
        return BoolNot(self)

    def __eq__(self, other):
        return BoolEqual(self, self.cast(other))

    def __hash__(self):
        return object.__hash__(self)

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
        # try to be forgiving. Allow user to use Bool in an IF sometimes
        from .visitors import simplify

        x = simplify(self)
        if isinstance(x, Constant):
            return x.value
        raise NotImplementedError("__bool__ for Bool")


class BoolVariable(Bool, Variable):
    __slots__ = Bool.__xslots__ + Variable.__xslots__

    @property
    def declaration(self):
        return f"(declare-fun {self.name} () Bool)"


class BoolConstant(Bool, Constant):
    __slots__ = Bool.__xslots__ + Constant.__xslots__

    def __init__(self, value, **kwargs):
        super().__init__(value=value, **kwargs)

    def __bool__(self):
        return self._value


class BoolOperation(Operation, Bool):
    __slots__ = ()
    __xslots__ = Operation.__xslots__ + Bool.__xslots__


class BoolNot(BoolOperation):
    __slots__ = BoolOperation.__xslots__

    def __init__(self, *args, **kwargs):
        super().__init__(operands=args, **kwargs)


class BoolAnd(BoolOperation):
    __slots__ = BoolOperation.__xslots__

    def __init__(self, *args, **kwargs):
        super().__init__(operands=args, **kwargs)


class BoolOr(BoolOperation):
    __slots__ = BoolOperation.__xslots__

    def __init__(self, *args, **kwargs):
        super().__init__(operands=args, **kwargs)


class BoolXor(BoolOperation):
    __slots__ = BoolOperation.__xslots__

    def __init__(self, *args, **kwargs):
        super().__init__(operands=args, **kwargs)


class BoolITE(BoolOperation):
    __slots__ = BoolOperation.__xslots__

    def __init__(self, cond: "Bool", true: "Bool", false: "Bool", **kwargs):
        super().__init__(operands=(cond, true, false), **kwargs)


class BitVec(Expression):
    __slots__ = ()
    __xslots__: Tuple[str, ...] = Expression.__xslots__ + ("size",)
    """ This adds a bitsize to the Expression class """

    def __init__(self, size: int, **kwargs):
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
        return LessThan(self, self.cast(other))

    def __le__(self, other):
        return LessOrEqual(self, self.cast(other))

    def __eq__(self, other):
        return BoolEqual(self, self.cast(other))

    def __hash__(self):
        return object.__hash__(self)

    def __ne__(self, other):
        return BoolNot(BoolEqual(self, self.cast(other)))

    def __gt__(self, other):
        return GreaterThan(self, self.cast(other))

    def __ge__(self, other):
        return GreaterOrEqual(self, self.cast(other))

    def __neg__(self):
        return BitVecNeg(self)

    # Unsigned comparisons
    def ugt(self, other):
        return UnsignedGreaterThan(self, self.cast(other))

    def uge(self, other):
        return UnsignedGreaterOrEqual(self, self.cast(other))

    def ult(self, other):
        return UnsignedLessThan(self, self.cast(other))

    def ule(self, other):
        return UnsignedLessOrEqual(self, self.cast(other))

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
    __slots__ = BitVec.__xslots__ + Variable.__xslots__

    def __init__(self, **kwargs):
        super().__init__(**kwargs)

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


class BitVecConstant(BitVec, Constant):
    __slots__ = BitVec.__xslots__ + Constant.__xslots__

    def __init__(self, size: int, value: int, **kwargs):
        value &= (1 << size) - 1
        super().__init__(size=size, value=value, **kwargs)

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


class BitVecOperation(BitVec, Operation):
    __xslots__ = BitVec.__xslots__ + Operation.__xslots__
    __slots__ = ()


class BitVecAdd(BitVecOperation):
    __slots__ = BitVecOperation.__xslots__

    def __init__(self, a, b, **kwargs):
        super().__init__(size=a.size, operands=(a, b), **kwargs)


class BitVecSub(BitVecOperation):
    __slots__ = BitVecOperation.__xslots__

    def __init__(self, a, b, **kwargs):
        super().__init__(size=a.size, operands=(a, b), **kwargs)


class BitVecMul(BitVecOperation):
    __slots__ = BitVecOperation.__xslots__

    def __init__(self, a, b, **kwargs):
        super().__init__(size=a.size, operands=(a, b), **kwargs)


class BitVecDiv(BitVecOperation):
    __slots__ = BitVecOperation.__xslots__

    def __init__(self, a, b, **kwargs):
        super().__init__(size=a.size, operands=(a, b), **kwargs)


class BitVecUnsignedDiv(BitVecOperation):
    __slots__ = BitVecOperation.__xslots__

    def __init__(self, a, b, **kwargs):
        super().__init__(size=a.size, operands=(a, b), **kwargs)


class BitVecMod(BitVecOperation):
    __slots__ = BitVecOperation.__xslots__

    def __init__(self, a, b, **kwargs):
        super().__init__(size=a.size, operands=(a, b), **kwargs)


class BitVecRem(BitVecOperation):
    __slots__ = BitVecOperation.__xslots__

    def __init__(self, a, b, **kwargs):
        super().__init__(size=a.size, operands=(a, b), **kwargs)


class BitVecUnsignedRem(BitVecOperation):
    __slots__ = BitVecOperation.__xslots__

    def __init__(self, a, b, **kwargs):
        super().__init__(size=a.size, operands=(a, b), **kwargs)


class BitVecShiftLeft(BitVecOperation):
    __slots__ = BitVecOperation.__xslots__

    def __init__(self, a, b, **kwargs):
        super().__init__(size=a.size, operands=(a, b), **kwargs)


class BitVecShiftRight(BitVecOperation):
    __slots__ = BitVecOperation.__xslots__

    def __init__(self, a, b, **kwargs):
        super().__init__(size=a.size, operands=(a, b), **kwargs)


class BitVecArithmeticShiftLeft(BitVecOperation):
    __slots__ = BitVecOperation.__xslots__

    def __init__(self, a, b, **kwargs):
        super().__init__(size=a.size, operands=(a, b), **kwargs)


class BitVecArithmeticShiftRight(BitVecOperation):
    __slots__ = BitVecOperation.__xslots__

    def __init__(self, a, b, **kwargs):
        super().__init__(size=a.size, operands=(a, b), **kwargs)


class BitVecAnd(BitVecOperation):
    __slots__ = BitVecOperation.__xslots__

    def __init__(self, a, b, *args, **kwargs):
        super().__init__(size=a.size, operands=(a, b), **kwargs)


class BitVecOr(BitVecOperation):
    __slots__ = BitVecOperation.__xslots__

    def __init__(self, a: BitVec, b: BitVec, *args, **kwargs):
        assert a.size == b.size
        super().__init__(size=a.size, operands=(a, b), **kwargs)


class BitVecXor(BitVecOperation):
    __slots__ = BitVecOperation.__xslots__

    def __init__(self, a, b, **kwargs):
        super().__init__(size=a.size, operands=(a, b), **kwargs)


class BitVecNot(BitVecOperation):
    __slots__ = BitVecOperation.__xslots__

    def __init__(self, a, **kwargs):
        super().__init__(size=a.size, operands=(a,), **kwargs)


class BitVecNeg(BitVecOperation):
    __slots__ = BitVecOperation.__xslots__

    def __init__(self, a, **kwargs):
        super().__init__(size=a.size, operands=(a,), **kwargs)


# Comparing two bitvectors results in a Bool
class LessThan(BoolOperation):
    __slots__ = BitVecOperation.__xslots__

    def __init__(self, a, b, *args, **kwargs):
        super().__init__(operands=(a, b), **kwargs)


class LessOrEqual(BoolOperation):
    __slots__ = BitVecOperation.__xslots__

    def __init__(self, a, b, *args, **kwargs):
        super().__init__(operands=(a, b), **kwargs)


class BoolEqual(BoolOperation):
    __slots__ = BitVecOperation.__xslots__

    def __init__(self, a, b, *args, **kwargs):
        if isinstance(a, BitVec) or isinstance(b, BitVec):
            assert a.size == b.size
        super().__init__(operands=(a, b), **kwargs)


class GreaterThan(BoolOperation):
    __slots__ = BitVecOperation.__xslots__

    def __init__(self, a, b, *args, **kwargs):
        super().__init__(operands=(a, b), **kwargs)


class GreaterOrEqual(BoolOperation):
    __slots__ = BitVecOperation.__xslots__

    def __init__(self, a, b, *args, **kwargs):
        assert a.size == b.size
        super().__init__(operands=(a, b), **kwargs)


class UnsignedLessThan(BoolOperation):
    __slots__ = BitVecOperation.__xslots__

    def __init__(self, a, b, **kwargs):
        super().__init__(operands=(a, b), **kwargs)


class UnsignedLessOrEqual(BoolOperation):
    __slots__ = BitVecOperation.__xslots__

    def __init__(self, a, b, **kwargs):
        assert a.size == b.size
        super().__init__(operands=(a, b), **kwargs)


class UnsignedGreaterThan(BoolOperation):
    __slots__ = BitVecOperation.__xslots__

    def __init__(self, a, b, *args, **kwargs):
        assert a.size == b.size
        super().__init__(operands=(a, b), **kwargs)


class UnsignedGreaterOrEqual(BoolOperation):
    __slots__ = BitVecOperation.__xslots__

    def __init__(self, a, b, **kwargs):
        super(UnsignedGreaterOrEqual, self).__init__(operands=(a, b), **kwargs)


###############################################################################
# Array  BV32 -> BV8  or BV64 -> BV8
class Array(Expression):
    __slots__ = (
        "_index_bits",
        "_index_max",
        "_value_bits",
        "_default",
        "_written",
        "_concrete_cache",
    )

    def __init__(
        self,
        index_bits: int,
        index_max: Optional[int],
        value_bits: int,
        default: Optional[int] = None,
        **kwargs,
    ):
        """
         This is a mapping from BV to BV. Normally used to represent a memory.

        :param index_bits: Number of bits in the addressing side
        :param index_max: Max address allowed
        :param value_bits: Number of bits in tha value side
        :param default: Reading from an uninitialized index will return default
                        if provided. If not the behaivor mimics thtat from smtlib,
                        the returned value is a free symbol.
        :param kwargs: Used in other parent classes
        """
        assert index_bits in (32, 64, 256)
        assert value_bits in (8, 16, 32, 64, 256)
        assert index_max is None or index_max >= 0 and index_max < 2 ** index_bits
        self._index_bits = index_bits
        self._index_max = index_max
        self._value_bits = value_bits
        self._default = default
        self._written = None  # Cache of the known indexs
        self._concrete_cache: Dict[int, int] = {}  # Cache of concrete indexes
        super().__init__(**kwargs)
        assert type(self) is not Array, "Abstract class"

    def _fix_slice(self, index: slice):
        """Used to calculate the size of slices"""
        stop, start = index.stop, index.start
        if start is None:
            start = 0
        if stop is None:
            stop = len(self)
        size = stop - start
        if isinstance(size, BitVec):
            from .visitors import simplify

            size = simplify(size)
        else:
            size = BitVecConstant(self.index_bits, size)
        assert isinstance(size, BitVecConstant)
        return start, stop, size.value

    def cast(self, possible_array):
        """ Builds an Array from a bytes or bytearray"""
        if isinstance(possible_array, (bytearray, bytes)):
            # FIXME This should be related to a constrainSet
            arr = ArrayVariable(
                self.index_bits, len(possible_array), 8, name="cast{}".format(uuid.uuid1())
            )
            for pos, byte in enumerate(possible_array):
                arr = arr.store(pos, byte)
            return arr
        raise ValueError  # cast not implemented

    def cast_index(self, index: Union[int, "BitVec"]) -> Union["BitVecConstant", "BitVec"]:
        if isinstance(index, int):
            # assert self.index_max is None or index >= 0 and index < self.index_max
            return BitVecConstant(self.index_bits, index)
        assert index.size == self.index_bits
        return index

    def cast_value(self, value: Union["BitVec", str, bytes, int]) -> "BitVec":
        if isinstance(value, BitVec):
            assert value.size == self.value_bits
            return value
        if isinstance(value, (str, bytes)) and len(value) == 1:
            value = ord(value)
        if not isinstance(value, int):
            value = int(value)
        return BitVecConstant(self.value_bits, value)

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

    @property
    def default(self):
        return self._default

    def get(self, index, default=None):
        """ Gets an element from the Array.
        If the element was not previously the default is used.
        """
        index = self.cast_index(index)

        # Emulate list[-1]
        if self.index_max is not None:
            from .visitors import simplify

            index = simplify(
                BitVecITE(self.index_bits, index < 0, self.index_max + index + 1, index)
            )

        if isinstance(index, Constant) and index.value in self._concrete_cache:
            return self._concrete_cache[index.value]
        value = ArraySelect(self, index)

        # No default. Returns free symbol
        if default is None:
            default = self._default
        if default is None:
            return value

        # If a default is provided calculate check if the index is known
        is_known = self.is_known(index)
        default = self.cast_value(default)
        if isinstance(is_known, Constant):
            if is_known.value:
                return value
            else:
                return default
        return BitVecITE(self.value_bits, is_known, value, default)

    def select(self, index):
        return self.get(index)

    def store(self, index, value):
        from .visitors import simplify

        index = simplify(self.cast_index(index))
        value = self.cast_value(value)
        new_array = ArrayStore(self, index, value)
        if isinstance(index, Constant):
            new_array._concrete_cache = copy.copy(self._concrete_cache)
            new_array._concrete_cache[index.value] = value
        else:
            # delete all cache as we do not know what this may overwrite.
            new_array._concrete_cache = {}
        if self.default is not None:
            # potentially generate and update .written set
            new_array.written.add(index)
        return new_array

    @property
    def written(self):
        # Calculate only first time
        if self._written is None:
            written = set()
            # take out Proxy sleve
            array = self
            offset = 0
            while not isinstance(array, ArrayVariable):
                if array._written is not None:
                    written = written.union((x - offset for x in array.written))
                    break
                if isinstance(array, ArraySlice):
                    # if it is a proxy over a slice take out the slice too
                    offset += array.slice_offset
                    array = array.array
                else:
                    # The index written to underlaying Array are displaced when sliced
                    written.add(array.index - offset)
                    array = array.array
            self._written = written
        return self._written

    def is_known(self, index):
        if isinstance(index, Constant) and index.value in self._concrete_cache:
            return BoolConstant(True)

        is_known_index = BoolConstant(False)
        written = self.written
        for known_index in written:
            if isinstance(index, Constant) and isinstance(known_index, Constant):
                if known_index.value == index.value:
                    return BoolConstant(True)
            is_known_index = BoolOr(is_known_index.cast(index == known_index), is_known_index)
        return is_known_index

    def write(self, offset, buf):
        """ Creates a new Array instance by writing buf at offset """
        if not isinstance(buf, (Array, bytes)):
            raise TypeError("Array or bytearray expected got {:s}".format(type(buf)))
        arr = self
        for i, val in enumerate(buf):
            arr = arr.store(offset + i, val)
        return arr

    def read(self, offset, size, default: Optional[int] = None):
        default = self._default if default is None else default
        return ArraySlice(self, offset=offset, size=size, default=default)

    def __getitem__(self, index):
        if isinstance(index, slice):
            start, stop, size = self._fix_slice(index)
            return self.read(start, size, self.default)
        else:
            if self.index_max is not None:
                if not isinstance(index, Expression) and index >= self.index_max:
                    raise IndexError
        return self.get(index, self._default)

    def __iter__(self):
        for i in range(len(self)):
            yield self[i]

    def __eq__(self, other):
        # FIXME taint
        def compare_buffers(a, b):
            if len(a) != len(b):
                return BoolConstant(False)
            cond = BoolConstant(True)
            for i in range(len(a)):
                cond = BoolAnd(cond.cast(a[i] == b[i]), cond)
                if cond is BoolConstant(False):
                    return BoolConstant(False)
            return cond

        return compare_buffers(self, other)

    def __ne__(self, other):
        return BoolNot(self == other)

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
            bytes.append(self.get(address + offset, self._default))
        return BitVecConcat(size * self.value_bits, *bytes)

    def read_LE(self, address, size):
        address = self.cast_index(address)
        bytes = []
        for offset in range(size):
            bytes.append(self.get(address + offset, self._default))
        return BitVecConcat(size * self.value_bits, *reversed(bytes))

    def write_BE(self, address, value, size):
        address = self.cast_index(address)
        value = BitVecConstant(size=size * self.value_bits, value=0).cast(value)
        array = self
        for offset in range(size):
            array = array.store(
                address + offset,
                BitVecExtract(value, (size - 1 - offset) * self.value_bits, self.value_bits),
            )
        return array

    def write_LE(self, address, value, size):
        address = self.cast_index(address)
        value = BitVec(size * self.value_bits).cast(value)
        array = self
        for offset in reversed(range(size)):
            array = array.store(
                address + offset,
                BitVecExtract(value, (size - 1 - offset) * self.value_bits, self.value_bits),
            )
        return array

    def __add__(self, other):
        if not isinstance(other, (Array, bytes)):
            raise TypeError("can't concat Array to {}".format(type(other)))
        if isinstance(other, Array):
            if self.index_bits != other.index_bits or self.value_bits != other.value_bits:
                raise ValueError("Array sizes do not match for concatenation")

        from .visitors import simplify

        # FIXME This should be related to a constrainSet
        new_arr = ArrayVariable(
            self.index_bits,
            self.index_max + len(other),
            self.value_bits,
            default=self._default,
            name="concatenation{}".format(uuid.uuid1()),
        )

        for index in range(self.index_max):
            new_arr = new_arr.store(index, simplify(self[index]))
        for index in range(len(other)):
            new_arr = new_arr.store(index + self.index_max, simplify(other[index]))
        return new_arr

    def __radd__(self, other):
        if not isinstance(other, (Array, bytes)):
            raise TypeError("can't concat Array to {}".format(type(other)))
        if isinstance(other, Array):
            if self.index_bits != other.index_bits or self.value_bits != other.value_bits:
                raise ValueError("Array sizes do not match for concatenation")

        from .visitors import simplify

        # FIXME This should be related to a constrainSet
        new_arr = ArrayVariable(
            self.index_bits,
            self.index_max + len(other),
            self.value_bits,
            default=self._default,
            name="concatenation{}".format(uuid.uuid1()),
        )

        for index in range(len(other)):
            new_arr = new_arr.store(index, simplify(other[index]))
        for index in range(self.index_max):
            new_arr = new_arr.store(index + len(other), simplify(self[index]))
        return new_arr


class ArrayVariable(Array, Variable):
    __slots__ = Array.__xslots__ + Variable.__xslots__

    @property
    def declaration(self):
        return f"(declare-fun {self.name} () (Array (_ BitVec {self.index_bits}) (_ BitVec {self.value_bits})))"


class ArrayOperation(Array, Operation):
    __slots__ = ()
    __xslots__ = Array.__xslots__ + Operation.__xslots__


class ArrayStore(ArrayOperation):
    __slots__ = ArrayOperation.__xslots__

    def __init__(self, array: "Array", index: "BitVec", value: "BitVec", **kwargs):
        assert index.size == array.index_bits
        assert value.size == array.value_bits
        super().__init__(
            index_bits=array.index_bits,
            value_bits=array.value_bits,
            index_max=array.index_max,
            default=array.default,
            operands=(array, index, value),
            **kwargs,
        )

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


class ArraySlice(ArrayOperation):
    """ Provides a projection of an underlying array.
        Lets you slice an array without copying it.
        (It needs to be simplified out before translating it smtlib)
    """

    __slots__ = ArrayOperation.__xslots__ + ("_slice_offset", "_slice_size")

    def __init__(
        self, array: "Array", offset: int, size: int, default: Optional[int] = None, **kwargs
    ):
        assert size
        if not isinstance(array, Array):
            raise ValueError("Array expected")
        if isinstance(array, ArrayProxy):
            array = array._array
        super().__init__(array, **kwargs)

        self._slice_offset = offset
        self._slice_size = size

    @property
    def array(self):
        return self.operands[0]

    @property
    def underlying_variable(self):
        return self.array.underlying_variable

    @property
    def index_bits(self):
        return self.array.index_bits

    @property
    def slice_offset(self):
        return self._slice_offset

    @property
    def value_bits(self):
        return self.array.value_bits

    def get(self, index, default):
        return self.array.get(index + self._slice_offset, default)

    def store(self, index, value):
        return ArraySlice(
            self.array.store(index + self._slice_offset, value),
            self._slice_offset,
            self._slice_size,
        )


class ArrayProxy:
    """
    Arrayproxy is a layer on top of an array that provides mutability and some
    simple optimizations for concrete indexes.

    It is not hasheable.
    Think:
        bytearray <-> ArrayProxy  ::: not hasheable, mutable
        bytes <-> Array (ArraySlice, ArrayVariable, ArrayStore) ::: hasheable, notmutable

    """

    def __hash__(self):
        return hash(self.array)

    def __init__(self, array: Array):
        self._array = array

    @property
    def underlying_variable(self):
        return self._array.underlying_variable

    @property
    def name(self):
        return self._array.name

    @property
    def array(self):
        return self._array

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

    def __len__(self):
        return len(self._array)

    def select(self, index):
        return self._array.select(index)

    def store(self, index, value):
        return self._array.store(index, value)

    @property
    def written(self):
        return self._array.written

    def __getitem__(self, index):
        result = self._array[index]
        if isinstance(index, slice):
            return ArrayProxy(result)
        return result

    def __setitem__(self, index, value):
        if isinstance(index, slice):
            start, stop, size = self._array._fix_slice(index)
            assert len(value) == size
            for i in range(size):
                self._array = self._array.store(start + i, value[i])
        else:
            self._array = self._array.store(index, value)

    def __copy__(self):
        return ArrayProxy(self.array)

    def get(self, index, default=None):
        return self._array.get(index, default)

    def write_BE(self, address, value, size):
        self._array = self._array.write_BE(address, value, size)

    def read_BE(self, address, size):
        return self._array.read_BE(address, size)

    def write(self, offset, buf):
        self._array = self._array.write(address, buf)

    def read(self, offset, size):
        return ArrayProxy(self._array[offset : offset + size])

    def __eq__(self, other):
        return other == self.array

    def __ne__(self, other):
        return BoolNot(self == other)

    def __add__(self, other):
        if not isinstance(other, (Array, ArrayProxy, bytes, bytearray)):
            raise TypeError("can't concat Array to {}".format(type(other)))
        if isinstance(other, Array):
            if self.index_bits != other.index_bits or self.value_bits != other.value_bits:
                raise ValueError("Array sizes do not match for concatenation")
        from .visitors import simplify

        # FIXME This should be related to a constrainSet
        new_arr = ArrayProxy(
            ArrayVariable(
                self.index_bits,
                self.index_max + len(other),
                self.value_bits,
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
            ArrayVariable(
                self.index_bits,
                self.index_max + len(other),
                self.value_bits,
                name="concatenation{}".format(uuid.uuid1()),
            )
        )
        for index in range(len(other)):
            new_arr[index] = simplify(other[index])
        for index in range(self.index_max):
            new_arr[index + len(other)] = simplify(self[index])
        return new_arr


class ArraySelect(BitVec, Operation):
    __slots__ = BitVec.__xslots__ + Operation.__xslots__

    def __init__(self, array: "Array", index: "BitVec", *args, **kwargs):
        assert index.size == array.index_bits
        super().__init__(size=array.value_bits, operands=(array, index), **kwargs)

    @property
    def array(self):
        return self.operands[0]

    @property
    def index(self):
        return self.operands[1]

    @property
    def operands(self):
        return self._operands

    def __repr__(self):
        return f"<ArraySelect obj with index={self.index}:\n{self.array}>"


class BitVecSignExtend(BitVecOperation):
    __slots__ = BitVecOperation.__xslots__ + ("extend",)

    def __init__(self, operand: "BitVec", size_dest: int, *args, **kwargs):
        assert size_dest >= operand.size
        super().__init__(size=size_dest, operands=(operand,), **kwargs)
        self.extend = size_dest - operand.size


class BitVecZeroExtend(BitVecOperation):
    __slots__ = BitVecOperation.__xslots__ + ("extend",)

    def __init__(self, size_dest: int, operand: "BitVec", *args, **kwargs):
        assert size_dest >= operand.size
        super().__init__(size=size_dest, operands=(operand,), **kwargs)
        self.extend = size_dest - operand.size


class BitVecExtract(BitVecOperation):
    __slots__ = BitVecOperation.__xslots__ + ("_begining", "_end")

    def __init__(self, operand: "BitVec", offset: int, size: int, *args, **kwargs):
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
    __slots__ = BitVecOperation.__xslots__

    def __init__(self, size_dest: int, *operands, **kwargs):
        assert all(isinstance(x, BitVec) for x in operands)
        assert size_dest == sum(x.size for x in operands)
        super().__init__(size=size_dest, operands=operands, **kwargs)


class BitVecITE(BitVecOperation):
    __slots__ = BitVecOperation.__xslots__

    def __init__(
        self,
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

