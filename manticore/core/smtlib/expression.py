from functools import reduce
import uuid

import re
import copy
from typing import Union, Optional, Dict, Tuple, List


class ExpressionError(Exception):
    """
    Expression exception
    """
    pass


class XSlotted(type):
    """ Metaclass that will propagate slots on multi-inheritance classes

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

        class X(object):
            __slots__ = ('a', 'b')

        c = C()
        c.a = 1
        c.b = 2

        x = X()
        x.a = 1
        x.b = 2

        import sys
        print (sys.getsizeof(c),sys.getsizeof(x))

    """

    def __new__(cls, clsname, bases, attrs, abstract=False):
        xslots = set(attrs.get("__xslots__", ()))
        for base in bases:
            xslots = xslots.union(getattr(base, "__xslots__", ()))
        attrs["__xslots__"] : Tuple[str, ...] = tuple(xslots)
        if abstract:
            attrs["__slots__"] = ()
        else:
            attrs["__slots__"]: Tuple[str, ...] = attrs["__xslots__"]

        return super().__new__(cls, clsname, bases, attrs)


class Expression(object, metaclass=XSlotted, abstract=True):
    """ Abstract taintable Expression. """

    __xslots__ : Tuple[str, ...] = ("_taint",)
    def __init__(self, taint: Union[tuple, frozenset] = ()):
        """
        An abstrac Unmutable Taintable Expression
        :param taint: A frozenzset
        """
        self._taint = frozenset(taint)
        super().__init__()

    def __repr__(self):
        return "<{:s} at {:x}{:s}>".format(type(self).__name__, id(self), self._taint and "-T" or "")

    @property
    def is_tainted(self):
        return len(self._taint) != 0

    @property
    def taint(self):
        return self._taint

    @property
    def operands(self):
        return ()

    def __getstate__(self):
        state = {}
        for attr in self.__slots__:
            if attr.startswith("__"):
                continue
            state[attr] = getattr(self, attr)
        return state

    def __setstate__(self, state):
        for attr in self.__slots__:
            if attr.startswith("__"):
                continue
            setattr(self, attr, state[attr])


    def __hash__(self):
        return object.__hash__(self)

class Variable(Expression, abstract=True):
    """ Variable is an Expression that has a name """

    __xslots__:Tuple[str, ...] = ("_name",)

    def __init__(self, name: str, **kwargs):
        """ Variable is an Expression that has a name
        :param name: The Variable name
        """
        super().__init__(**kwargs)
        self._name = name

    @property
    def name(self):
        return self._name

    def __repr__(self):
        return "<{:s}({:s}) at {:x}>".format(type(self).__name__, self.name, id(self))


    def __hash__(self):
        return object.__hash__(self)


class Constant(Expression, abstract=True):
    """ Constants expressions have a concrete python value. """

    __xslots__:Tuple[str, ...] = ("_value",)

    def __init__(self, value: Union[bool, int, bytes, List[int]], **kwargs):
        """ A constant expression has a value

        :param value: The constant value
        """
        super().__init__(**kwargs)
        self._value = value

    @property
    def value(self):
        return self._value


    def __hash__(self):
        return object.__hash__(self)

class Operation(Expression, abstract=True):
    """ Operation expressions contain operands which are also Expressions. """

    __xslots__:Tuple[str, ...] = ("_operands",)

    def __init__(self, operands: Tuple[Expression, ...], **kwargs):
        """ An operation has operands

        :param operands: A tuple of expression operands
        """
        taint = kwargs.get('taint')
        assert isinstance(operands, tuple)
        print ("Operation of operands", type(self) ,tuple(map(type,operands)))
        self._operands = operands
        # If taint was not forced by a keyword argument, calculate default
        if taint is None:
            operands_taints = map(lambda x: x.taint, operands)
            taint = reduce(lambda x, y: x.union(y), operands_taints, frozenset())
        kwargs['taint'] = taint
        super().__init__(**kwargs)

    @property
    def operands(self):
        return self._operands

    def __hash__(self):
        return object.__hash__(self)

###############################################################################
# Booleans
class Bool(Expression, abstract=True):
    """Bool expression represent symbolic value of truth"""
    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)

    def cast(self, value: Union["Bool", int, bool], **kwargs) -> Union["BoolConstant", "Bool"]:
        if isinstance(value, Bool):
            return value
        return BoolConstant(bool(value), **kwargs)

    def __cmp__(self, *args):
        raise NotImplementedError("CMP for Bool")

    def __invert__(self):
        return BoolNot(self)

    def __eq__(self, other):
        # A class that overrides __eq__() and does not define __hash__()
        # will have its __hash__() implicitly set to None.
        #import pdb; pdb.set_trace()
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
        raise NotImplementedError
    """
    def __bool__(self):
        # try to be forgiving. Allow user to use Bool in an IF sometimes
        from .visitors import simplify
        x = simplify(self)
        if isinstance(x, Constant):
            return x.value
        raise NotImplementedError("__bool__ for Bool")
    """


class BoolVariable(Bool, Variable):
    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)


class BoolConstant(Bool, Constant):
    def __init__(self, value: bool, **kwargs):
        super().__init__(value=bool(value), **kwargs)

    def __bool__(self):
        return self._value

    def __eq__(self, other):
        # A class that overrides __eq__() and does not define __hash__()
        # will have its __hash__() implicitly set to None.
        if self.taint:
            return super().__eq__(other)
        return self.value == other

    def __hash__(self):
        return object.__hash__(self)


class BoolOperation(Bool, Operation, abstract=True):
    """ It's an operation that results in a Bool """
    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)

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


class Bitvec(Expression, abstract=True):
    """ Bitvector expressions have a fixed bit size """

    __xslots__:Tuple[str, ...] = ("_size",)

    def __init__(self, size: int, **kwargs):
        """  This is bit vector expression

        :param size: number of buts used
        """
        super().__init__(**kwargs)
        self._size = size

    @property
    def size(self):
        return self._size

    @property
    def mask(self):
        return (1 << self.size) - 1

    @property
    def signmask(self):
        return 1 << (self.size - 1)

    def cast(
        self, value: Union["Bitvec", str, int, bytes], **kwargs
    ) -> "Bitvec":
        if isinstance(value, Bitvec):
            assert value.size == self.size
            return value
        if isinstance(value, (str, bytes)) and len(value) == 1:
            print ("AAAAAAAAAA"*99)
            value = ord(value)
        # Try to support not Integral types that can be casted to int
        if not isinstance(value, int):
            print (value)
            value = int(value)
        # FIXME? Assert it fits in the representation
        return BitvecConstant(self.size, value, **kwargs)

    def __add__(self, other):
        return BitvecAdd(self, self.cast(other))

    def __sub__(self, other):
        return BitvecSub(self, self.cast(other))

    def __mul__(self, other):
        return BitvecMul(self, self.cast(other))

    def __mod__(self, other):
        return BitvecMod(self, self.cast(other))

    # object.__divmod__(self, other)
    # object.__pow__(self, other[, modulo])

    def __lshift__(self, other):
        return BitvecShiftLeft(self, self.cast(other))

    def __rshift__(self, other):
        return BitvecShiftRight(self, self.cast(other))

    def __and__(self, other):
        return BitvecAnd(self, self.cast(other))

    def __xor__(self, other):
        return BitvecXor(self, self.cast(other))

    def __or__(self, other):
        return BitvecOr(self, self.cast(other))

    # The division operator (/) is implemented by these methods. The
    # __truediv__() method is used when __future__.division is in effect,
    # otherwise __div__() is used. If only one of these two methods is
    # defined, the object will not support division in the alternate context;
    # TypeError will be raised instead.

    def __div__(self, other):
        return BitvecDiv(self, self.cast(other))

    def __truediv__(self, other):
        return BitvecDiv(self, self.cast(other))

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
        return BitvecAdd(self.cast(other), self)

    def __rsub__(self, other):
        return BitvecSub(self.cast(other), self)

    def __rmul__(self, other):
        return BitvecMul(self.cast(other), self)

    def __rmod__(self, other):
        return BitvecMod(self.cast(other), self)

    def __rtruediv__(self, other):
        return BitvecDiv(self.cast(other), self)

    def __rdiv__(self, other):
        return BitvecDiv(self.cast(other), self)

    # object.__rdivmod__(self, other)
    # object.__rpow__(self, other)

    def __rlshift__(self, other):
        return BitvecShiftLeft(self.cast(other), self)

    def __rrshift__(self, other):
        return BitvecShiftRight(self.cast(other), self)

    def __rand__(self, other):
        return BitvecAnd(self.cast(other), self)

    def __rxor__(self, other):
        return BitvecXor(self.cast(other), self)

    def __ror__(self, other):
        return BitvecOr(self.cast(other), self)

    def __invert__(self):
        return BitvecXor(self, self.cast(self.mask))

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

    def __hash__(self):
        return object.__hash__(self)

    def __ne__(self, other):
        return BoolNot(BoolEqual(self, self.cast(other)))

    def __gt__(self, other):
        return BoolGreaterThan(self, self.cast(other))

    def __ge__(self, other):
        return BoolGreaterOrEqualThan(self, self.cast(other))

    def __neg__(self):
        return BitvecNeg(self)

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
        return BitvecUnsignedDiv(self, self.cast(other))

    def rudiv(self, other):
        return BitvecUnsignedDiv(self.cast(other), self)

    def sdiv(self, other):
        return BitvecDiv(self, self.cast(other))

    def rsdiv(self, other):
        return BitvecDiv(self.cast(other), self)

    def srem(self, other):
        return BitvecRem(self, self.cast(other))

    def rsrem(self, other):
        return BitvecRem(self.cast(other), self)

    def urem(self, other):
        return BitvecUnsignedRem(self, self.cast(other))

    def rurem(self, other):
        return BitvecUnsignedRem(self.cast(other), self)

    def sar(self, other):
        return BitvecArithmeticShiftRight(self, self.cast(other))

    def sal(self, other):
        return BitvecArithmeticShiftLeft(self, self.cast(other))

    def Bool(self):
        return self != 0


class BitvecVariable(Bitvec, Variable):
    def __repr__(self):
        return "<{:s}({:s}) at {:x}>".format(type(self).__name__, self.name, id(self))


class BitvecConstant(Bitvec, Constant):
    def __init__(self, size: int, value: int, **kwargs):
        value &= (1 << size) - 1
        super().__init__(size=size, value=value, **kwargs)

    def __bool__(self):
        return self.value != 0

    def __int__(self):
        return self.value

    @property
    def signed_value(self):
        if self._value & self.signmask:
            return self._value - (1 << self.size)
        else:
            return self._value

    def __eq__(self, other):
        if self.taint or isinstance(other, Expression) and other.taint:
            return super().__eq__(other)
        print (self.value, other)
        return self.value == other

    def __hash__(self):
        return object.__hash__(self)

class BitvecOperation(Bitvec, Operation, abstract=True):
    """ Operations that result in a Bitvec """
    pass


class BitvecAdd(BitvecOperation):
    def __init__(self, operanda, operandb, **kwargs):
        super().__init__(size=operanda.size, operands=(operanda, operandb), **kwargs)


class BitvecSub(BitvecOperation):
    def __init__(self, operanda, operandb, **kwargs):
        super().__init__(size=operanda.size, operands=(operanda, operandb), **kwargs)


class BitvecMul(BitvecOperation):
    def __init__(self, operanda, operandb, **kwargs):
        super().__init__(size=operanda.size, operands=(operanda, operandb), **kwargs)


class BitvecDiv(BitvecOperation):
    def __init__(self, operanda, operandb, **kwargs):
        super().__init__(size=operanda.size, operands=(operanda, operandb), **kwargs)


class BitvecUnsignedDiv(BitvecOperation):
    def __init__(self, operanda, operandb, **kwargs):
        super().__init__(size=operanda.size, operands=(operanda, operandb), **kwargs)


class BitvecMod(BitvecOperation):
    def __init__(self, operanda, operandb, **kwargs):
        super().__init__(size=operanda.size, operands=(operanda, operandb), **kwargs)


class BitvecRem(BitvecOperation):
    def __init__(self, operanda, operandb, **kwargs):
        super().__init__(size=operanda.size, operands=(operanda, operandb), **kwargs)


class BitvecUnsignedRem(BitvecOperation):
    def __init__(self, operanda, operandb, **kwargs):
        super().__init__(size=operanda.size, operands=(operanda, operandb), **kwargs)


class BitvecShiftLeft(BitvecOperation):
    def __init__(self, operanda, operandb, **kwargs):
        super().__init__(size=operanda.size, operands=(operanda, operandb), **kwargs)


class BitvecShiftRight(BitvecOperation):
    def __init__(self, operanda, operandb, **kwargs):
        super().__init__(size=operanda.size, operands=(operanda, operandb), **kwargs)


class BitvecArithmeticShiftLeft(BitvecOperation):
    def __init__(self, operanda, operandb, **kwargs):
        super().__init__(size=operanda.size, operands=(operanda, operandb), **kwargs)


class BitvecArithmeticShiftRight(BitvecOperation):
    def __init__(self, operanda, operandb, **kwargs):
        super().__init__(size=operanda.size, operands=(operanda, operandb), **kwargs)


class BitvecAnd(BitvecOperation):
    def __init__(self, operanda, operandb, *args, **kwargs):
        super().__init__(size=operanda.size, operands=(operanda, operandb), **kwargs)


class BitvecOr(BitvecOperation):
    def __init__(self, operanda: Bitvec, operandb: Bitvec, *args, **kwargs):
        super().__init__(size=operanda.size, operands=(operanda, operandb), **kwargs)


class BitvecXor(BitvecOperation):
    def __init__(self, operanda, operandb, **kwargs):
        super().__init__(size=operanda.size, operands=(operanda, operandb), **kwargs)


class BitvecNot(BitvecOperation):
    def __init__(self, operanda, **kwargs):
        super().__init__(size=operanda.size, operands=(operanda,), **kwargs)


class BitvecNeg(BitvecOperation):
    def __init__(self, operanda, **kwargs):
        super().__init__(size=operanda.size, operands=(operanda,), **kwargs)


# Comparing two bitvectors results in a Bool
class BoolLessThan(BoolOperation):
    def __init__(self, operanda: Bitvec, operandb: Bitvec, **kwargs):
        super().__init__(operands=(operanda, operandb), **kwargs)


class BoolLessOrEqualThan(BoolOperation):
    def __init__(self, operanda: Bitvec, operandb: Bitvec, **kwargs):
        super().__init__(operands=(operanda, operandb), **kwargs)


class BoolEqual(BoolOperation):
    def __init__(self, operanda: Bitvec, operandb: Bitvec, **kwargs):
        assert isinstance(operanda, Expression)
        assert isinstance(operandb, Expression)
        super().__init__(operands=(operanda, operandb), **kwargs)


class BoolGreaterThan(BoolOperation):
    def __init__(self, operanda: Bitvec, operandb: Bitvec, **kwargs):
        super().__init__(operands=(operanda, operandb), **kwargs)


class BoolGreaterOrEqualThan(BoolOperation):
    def __init__(self, operanda: Bitvec, operandb: Bitvec, *args, **kwargs):
        super().__init__(operands=(operanda, operandb), **kwargs)


class BoolUnsignedLessThan(BoolOperation):
    def __init__(self, operanda: Bitvec, operandb: Bitvec, **kwargs):
        super().__init__(operands=(operanda, operandb), **kwargs)


class BoolUnsignedLessOrEqualThan(BoolOperation):
    def __init__(self, operanda: Bitvec, operandb: Bitvec, **kwargs):
        super().__init__(operands=(operanda, operandb), **kwargs)


class BoolUnsignedGreaterThan(BoolOperation):
    def __init__(self, operanda, operandb, *args, **kwargs):
        super().__init__(operands=(operanda, operandb), **kwargs)


class BoolUnsignedGreaterOrEqualThan(BoolOperation):
    def __init__(self, operanda, operandb, **kwargs):
        super(BoolUnsignedGreaterOrEqualThan, self).__init__(
            operands=(operanda, operandb), **kwargs
        )


###############################################################################
# Array  BV32 -> BV8  or BV64 -> BV8
class Array(Expression, abstract=True):
    """ And Array expression is a mapping from bitvector to bitvectors
    """
    @property
    def index_size(self):
        """ The bit size of the index part. Must be overloaded by a more specific class"""
        raise NotImplementedError

    @property
    def value_size(self):
        """ The bit size of the value part. Must be overloaded by a more specific class"""
        raise NotImplementedError

    @property
    def index_max(self):
        """ Max allowed index. Must be overloaded by a more specific class"""
        raise NotImplementedError

    def get(self, index):
        """ Gets an element from the Array """
        raise NotImplementedError

    def store(self, index, value):
        raise NotImplementedError

    ## following methods are implementes on top of the abstract methods ^
    def cast(self, possible_array):
        """ Builds an Array from a bytes or bytearray"""
        # FIXME This should be related to a constrainSet
        arr = ArrayVariable(
            index_size=self.index_size, length=len(possible_array), value_size=self.value_size, name="cast{}".format(uuid.uuid1())
        )
        for pos, byte in enumerate(possible_array):
            arr = arr.store(pos, byte)
        return arr

    def cast_index(self, index: Union[int, Bitvec]) -> Bitvec:
        """ Forgiving casting method that will translate compatible values into
            a complant BitVec for indexing"""
        if isinstance(index, int):
            return BitvecConstant(self.index_size, index)
        if index.size != self.index_size:
            raise ValueError

        return simplify(index)
        #return index

    def cast_value(self, value: Union[Bitvec, bytes, int]) -> Bitvec:
        """ Forgiving casting method that will translate compatible values into
            a complant BitVec to ve used as a value"""
        if not isinstance(value, (Bitvec, bytes, int)):
            raise TypeError
        if isinstance(value, Bitvec):
            if value.size != self.value_size:
                raise ValueError
            return value
        if isinstance(value, bytes) and len(value) == 1:
            value = ord(value)
        if not isinstance(value, int):
            print (value, type(value))
            value = int(value)
        return BitvecConstant(self.value_size, value)

    def __len__(self):
        print (self.index_max)
        return self.index_max+1

    def select(self, index):
        return self.get(index)

    def write(self, offset, buf):
        """ Creates a new Array instance by writing buf at offset """
        arr = self
        for i, val in enumerate(buf):
            arr = arr.store(offset + i, val)
        return arr

    def read(self, offset, size):
        return ArraySlice(self, offset=offset, size=size)

    def __getitem__(self, index):
        if isinstance(index, slice):
            start, stop, size = self._fix_slice(index)
            return self.read(start, size)
        return self.select(index)

    def __iter__(self):
        for i in range(len(self)):
            yield self[i]

    def __eq__(self, other):
        # FIXME taint
        def compare_buffers(a, b):
            print (type(a))
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

    def _fix_slice(self, index: slice):
        """Used to calculate the size of slices"""
        stop, start = index.stop, index.start
        if start is None:
            start = 0
        if stop is None:
            stop = len(self)
        size = stop - start
        if isinstance(size, Bitvec):
            from .visitors import simplify

            size = simplify(size)
        else:
            size = BitvecConstant(self.index_size, size)
        assert isinstance(size, BitvecConstant)
        return start, stop, size.value



class ArrayConstant(Array, Constant):
    __xslots__: Tuple[str, ...] = (
            "_index_size",
            "_value_size")

    def __init__(
        self, *,
        index_size: int,
        value_size: int,
        **kwargs,
    ):
        self._index_size = index_size
        self._value_size = value_size
        super().__init__(**kwargs)

    @property
    def index_size(self):
        return self._index_size

    @property
    def value_size(self):
        return self._value_size

    @property
    def index_max(self):
        return len(self.value)

    def get(self, index):
        index = self.cast_index(index)
        if isinstance(index, Constant):
            return BitvecConstant(size=self.value_size, value=self.value[index.value], taint=self.taint)
        result = BitvecConstant(size=self.value_size, value=0, taint=('out_of_bounds'))
        for i, c in enumerate(self.value):
            result = BitvecITE(index == i, BitvecConstant(size=self.value_size, value=c), result, taint=self.taint)
        return result

    def read(self, offset, size):
        assert (len(self.value[offset:offset + size]) == size)
        return ArrayConstant(index_size=self.index_size, value_size=self.value_size, value=self.value[offset:offset+size])


class ArrayVariable(Array, Variable):
    """
    An Array expression is a mapping from bitvector of index_size bits
    into bitvectors of value_size bits.

    If a default value is provided reading from an unused index will return the
    default. Otherwise each unused position in the array represents a free bitvector.

    If an index_max maximun index is provided accessing over the max is undefined.
    Otherwise the array is unbounded.

    """
    __xslots__: Tuple[str, ...] = (
            "_index_size",
            "_value_size",
            "_length",
            "_default",
        )


    def __hash__(self):
        return object.__hash__(self)

    def __init__(
        self,
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
        assert length is None or length >= 0 and length < 2 ** index_size
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
    def index_max(self):
        if self._length is None:
            return None
        return int(self._length) - 1

    @property
    def default(self):
        return self._default

    def get(self, index, default=None):
        """ Gets an element from the Array.
        If the element was not previously the default is used.
        """
        if default is None:
            default = self._default
        if default is not None:
            return default
        index = self.cast_index(index)
        return ArraySelect(self, index)

    def select(self, index):
        return self.get(index)

    def store(self, index, value):
        index = self.cast_index(index)
        value = self.cast_value(value)
        return ArrayStore(array=self, index=index, value=value)

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
                    offset += array.offset
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
        return BitvecConcat(*bytes)

    def read_LE(self, address, size):
        address = self.cast_index(address)
        bytes = []
        for offset in range(size):
            bytes.append(self.get(address + offset, self._default))
        return BitvecConcat(size * self.value_size, *reversed(bytes))

    def write_BE(self, address, value, size):
        address = self.cast_index(address)
        value = BitvecConstant(size=size * self.value_size, value=0).cast(value)
        array = self
        for offset in range(size):
            array = array.store(
                address + offset,
                BitvecExtract(value, (size - 1 - offset) * self.value_size, self.value_size),
            )
        return array

    def write_LE(self, address, value, size):
        address = self.cast_index(address)
        value = Bitvec(size * self.value_size).cast(value)
        array = self
        for offset in reversed(range(size)):
            array = array.store(
                address + offset,
                BitvecExtract(value, (size - 1 - offset) * self.value_size, self.value_size),
            )
        return array

    def __add__(self, other):
        if not isinstance(other, (Array, bytes)):
            raise TypeError("can't concat Array to {}".format(type(other)))
        if isinstance(other, Array):
            if self.index_size != other.index_size or self.value_size != other.value_size:
                raise ValueError("Array sizes do not match for concatenation")

        # FIXME This should be related to a constrainSet
        new_arr = ArrayVariable(
            self.index_size,
            self.index_max + len(other),
            self.value_size,
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
            if self.index_size != other.index_size or self.value_size != other.value_size:
                raise ValueError("Array sizes do not match for concatenation")

        from .visitors import simplify

        # FIXME This should be related to a constrainSet
        new_arr = ArrayVariable(
            self.index_size,
            self.index_max + len(other),
            self.value_size,
            default=self._default,
            name="concatenation{}".format(uuid.uuid1()),
        )

        for index in range(len(other)):
            new_arr = new_arr.store(index, simplify(other[index]))
        for index in range(self.index_max):
            new_arr = new_arr.store(index + len(other), simplify(self[index]))
        return new_arr



class ArrayOperation(Array, Operation, abstract=True):
    """ It's an operation that results in an Array"""
    pass


class ArrayStore(ArrayOperation):
    __xslots__: Tuple[str, ...] = (
        "_written",
        "_concrete_cache",
    )
    def __init__(self, array: Array, index: Bitvec, value: Bitvec, **kwargs):
        assert index.size == array.index_size
        assert value.size == array.value_size
        self._written = None  # Cache of the known indexs
        self._concrete_cache = {}
        if isinstance(index, Constant):
            self._concrete_cache.update(getattr(array, "_concrete_cache", ()))  # Cache of concrete indexes
            self._concrete_cache[index.value] = value
        super().__init__(
            operands=(array, index, value),
            **kwargs,
        )

    @property
    def default(self):
        return self.array.default

    @property
    def index_size(self):
        return self.index.size

    @property
    def value_size(self):
        return self.value.size

    @property
    def index_max(self):
        return self.array.index_max

    def __hash__(self):
        return object.__hash__(self)

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

    def get(self, index, default=None):
        """ Gets an element from the Array.
        If the element was not previously the default is used.
        """
        index = simplify(self.cast_index(index))

        # Emulate list[-1]
        if self.index_max is not None:
            index = simplify(
                BitvecITE(index < 0, self.index_max + index + 1, index)
            )

        if isinstance(index, Constant):
            if self.index_max is not None and index.value > self.index_max:
                raise IndexError
            if index.value in self._concrete_cache:
                return self._concrete_cache[index.value]

        # take out Proxy sleve
        if default is None:
            default = self.default
        if default is None:
            # No default. Returns normal array select
            return ArraySelect(self, index)

        # build a big ITE expression that would en in the default
        array, offset, items = self, 0, []
        while not isinstance(array, ArrayVariable):
            if isinstance(array, ArraySlice):
                # jump over array slices
                offset += array.offset
            else:
                # The index written to underlaying Array are displaced when sliced
                items.insert(0, (index == (array.index - offset), array.value))
            array = array.array

        result = self.cast_value(default)
        for cond_i, value_i in items:
            result = BitvecITE(cond_i, value_i, result)
        return result

    def store(self, index, value):
        index = simplify(self.cast_index(index))
        value = self.cast_value(value)
        new_array = ArrayStore(self, index, value)
        return new_array


class ArraySlice(ArrayOperation):
    """ Provides a projection of an underlying array.
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
    def index_max(self):
        return self.operands[2].value-1

    @property
    def index_size(self):
        return self.array.index_size

    @property
    def value_size(self):
        return self.array.value_size

    @property
    def underlying_variable(self):
        return self.array.underlying_variable

    def get(self, index, default=None):
        index = self.cast_index(index)
        if isinstance(index, Constant):
            if self.index_max is not None and index.value >= len(self):
                raise IndexError
        return self.array.get(simplify(index + self.offset), default)

    def store(self, index, value):
        return ArraySlice(
            self.array.store(index + self.offset, value),
            offset=self.offset,
            size=len(self),
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

    def __init__(self, array: Array):
        assert isinstance(array, Array)
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
    def index_size(self):
        return self._array.index_size

    @property
    def index_max(self):
        return self._array.index_max

    @property
    def value_size(self):
        return self._array.value_size

    @property
    def taint(self):
        return self._array.taint

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
        assert self._array is not None


    def get(self, index, default=None):
        x  = self._array.get(index, default)
        print ("A"*199, type(self._array), "X:", x)
        return x

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
        return ArrayProxy(self._array[offset : offset + size])

    def __eq__(self, other):
        print ("type:"*99, type(self.array ), type(other))
        return self.array == other

    def __ne__(self, other):
        return BoolNot(self == other)

    def _concatenate(self, array_a, array_b):
        from .visitors import simplify
        # FIXME/Research This should be related to a constrainSet
        new_arr = ArrayProxy(
            ArrayVariable(
                index_size = self.index_size,
                length=len(array_a) + len(array_b),
                value_size = self.value_size,
                name="concatenation{}".format(uuid.uuid1()),
            )
        )
        for index in range(len(array_a)):
            new_arr[index] = simplify(array_a[index])
        for index in range(len(array_b)):
            new_arr[index + len(array_a)] = simplify(array_b[index])
        return new_arr

    def __add__(self, other):
        return self._concatenate(self, other)

    def __radd__(self, other):
        return self._concatenate(other, self)

class ArraySelect(BitvecOperation):
    __xslots__ = BitvecOperation.__xslots__

    def __init__(self, array: "Array", index: "Bitvec", *args, **kwargs):
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


class BitvecSignExtend(BitvecOperation):
    def __init__(self, operand: Bitvec, size: int, *args, **kwargs):
        super().__init__(size=size, operands=(operand,), **kwargs)

    @property
    def extend(self):
        return self.size - self.operands[0].size



class BitvecZeroExtend(BitvecOperation):
    def __init__(self, size: int, operand: Bitvec, *args, **kwargs):
        super().__init__(size=size, operands=(operand,), **kwargs)

    @property
    def extend(self):
         return self.size - self.operands[0].size


class BitvecExtract(BitvecOperation):
    __xslots__ = ("_offset",)

    def __init__(self, operand: "Bitvec", offset: int, size: int, *args, **kwargs):
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


class BitvecConcat(BitvecOperation):

    def __init__(self, operands: Tuple[Bitvec, ...], **kwargs):
        size = sum(x.size for x in operands)
        super().__init__(size=size, operands=operands, **kwargs)


class BitvecITE(BitvecOperation):
    __xslots__ = BitvecOperation.__xslots__

    def __init__(
        self,
        condition: Bool,
        true_value: Bitvec,
        false_value: Bitvec,
        **kwargs,
    ):

        super().__init__(size=true_value.size, operands=(condition, true_value, false_value), **kwargs)

    @property
    def condition(self):
        return self.operands[0]

    @property
    def true_value(self):
        return self.operands[1]

    @property
    def false_value(self):
        return self.operands[2]


# auxiliar functions maybe move to operators
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


def taint_with(arg, *taints, value_size=256, index_size=256):
    """
    Helper to taint a value.
    :param arg: a value or Expression
    :param taint: a regular expression matching a taint value (eg. 'IMPORTANT.*'). If None, this function checks for any taint value.
    """
    tainted_fset = frozenset(tuple(taints))
    if not issymbolic(arg):
        if isinstance(arg, int):
            arg = BitvecConstant(value_size, arg)
            arg._taint = tainted_fset
        else:
            raise ValueError("type not supported")

    else:
        arg = copy.copy(arg)
        arg._taint |= tainted_fset

    return arg


from .visitors import simplify
