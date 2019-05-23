from functools import reduce
import uuid


class Expression:
    """ Abstract taintable Expression. """

    def __init__(self, taint=()):
        if self.__class__ is Expression:
            raise TypeError
        assert isinstance(taint, (tuple, frozenset))
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


class Variable(Expression):
    def __init__(self, name, *args, **kwargs):
        if self.__class__ is Variable:
            raise TypeError
        assert isinstance(name, str) and " " not in name
        super().__init__(*args, **kwargs)
        self._name = name

    @property
    def declaration(self):
        pass

    @property
    def name(self):
        return self._name

    def __copy__(self, memo):
        raise Exception("Copying of Variables is not allowed.")

    def __deepcopy__(self, memo):
        raise Exception("Copying of Variables is not allowed.")

    def __repr__(self):
        return "<{:s}({:s}) at {:x}>".format(type(self).__name__, self.name, id(self))


class Constant(Expression):
    def __init__(self, value, *args, **kwargs):
        if self.__class__ is Constant:
            raise TypeError
        assert isinstance(value, (bool, int))
        super().__init__(*args, **kwargs)
        self._value = value

    @property
    def value(self):
        return self._value


class Operation(Expression):
    def __init__(self, *operands, **kwargs):
        if self.__class__ is Operation:
            raise TypeError
        # assert len(operands) > 0
        # assert all(isinstance(x, Expression) for x in operands)
        self._operands = operands

        # If taint was not forced by a keyword argument, calculate default
        if "taint" not in kwargs:
            kwargs["taint"] = reduce(lambda x, y: x.union(y.taint), operands, frozenset())

        super().__init__(**kwargs)

    @property
    def operands(self):
        return self._operands


###############################################################################
# Booleans
class Bool(Expression):
    def __init__(self, *operands, **kwargs):
        super().__init__(*operands, **kwargs)

    def cast(self, value, **kwargs):
        if isinstance(value, Bool):
            return value
        assert isinstance(value, (int, bool))
        return BoolConstant(bool(value), **kwargs)

    def __cmp__(self, *args):
        raise NotImplementedError("CMP for Bool")

    def __invert__(self):
        return BoolNot(self)

    def __eq__(self, other):
        return BoolEq(self, self.cast(other))

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
        raise NotImplementedError("__bool__ for Bool")


class BoolVariable(Bool, Variable):
    def __init__(self, name, *args, **kwargs):
        super().__init__(name, *args, **kwargs)

    @property
    def declaration(self):
        return f"(declare-fun {self.name} () Bool)"


class BoolConstant(Bool, Constant):
    def __init__(self, value, *args, **kwargs):
        assert isinstance(value, bool)
        super().__init__(value, *args, **kwargs)

    def __bool__(self):
        return self.value


class BoolOperation(Operation, Bool):
    def __init__(self, *operands, **kwargs):
        super().__init__(*operands, **kwargs)


class BoolNot(BoolOperation):
    def __init__(self, value, **kwargs):
        super().__init__(value, **kwargs)


class BoolEq(BoolOperation):
    def __init__(self, a, b, **kwargs):
        super().__init__(a, b, **kwargs)


class BoolAnd(BoolOperation):
    def __init__(self, a, b, **kwargs):
        super().__init__(a, b, **kwargs)


class BoolOr(BoolOperation):
    def __init__(self, a, b, **kwargs):
        assert isinstance(a, Bool)
        assert isinstance(b, Bool)
        super().__init__(a, b, **kwargs)


class BoolXor(BoolOperation):
    def __init__(self, a, b, **kwargs):
        super().__init__(a, b, **kwargs)


class BoolITE(BoolOperation):
    def __init__(self, cond, true, false, **kwargs):
        assert isinstance(true, Bool)
        assert isinstance(false, Bool)
        assert isinstance(cond, Bool)
        super().__init__(cond, true, false, **kwargs)


class BitVec(Expression):
    """ This adds a bitsize to the Expression class """

    def __init__(self, size, *operands, **kwargs):
        super().__init__(*operands, **kwargs)
        self.size = size

    @property
    def mask(self):
        return (1 << self.size) - 1

    @property
    def signmask(self):
        return 1 << (self.size - 1)

    def cast(self, value, **kwargs):
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
        return Equal(self, self.cast(other))

    def __hash__(self):
        return object.__hash__(self)

    def __ne__(self, other):
        return BoolNot(Equal(self, self.cast(other)))

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
    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)

    @property
    def declaration(self):
        return f"(declare-fun {self.name} () (_ BitVec {self.size}))"


class BitVecConstant(BitVec, Constant):
    def __init__(self, size, value, *args, **kwargs):
        assert isinstance(value, int)
        super().__init__(size, value, *args, **kwargs)

    def __bool__(self):
        return self.value != 0

    def __eq__(self, other):
        if self.taint:
            return super().__eq__(other)
        return self.value == other

    def __hash__(self):
        return super().__hash__()


class BitVecOperation(BitVec, Operation):
    def __init__(self, size, *operands, **kwargs):
        super().__init__(size, *operands, **kwargs)


class BitVecAdd(BitVecOperation):
    def __init__(self, a, b, *args, **kwargs):
        super().__init__(a.size, a, b, *args, **kwargs)


class BitVecSub(BitVecOperation):
    def __init__(self, a, b, *args, **kwargs):
        super().__init__(a.size, a, b, *args, **kwargs)


class BitVecMul(BitVecOperation):
    def __init__(self, a, b, *args, **kwargs):
        super().__init__(a.size, a, b, *args, **kwargs)


class BitVecDiv(BitVecOperation):
    def __init__(self, a, b, *args, **kwargs):
        super().__init__(a.size, a, b, *args, **kwargs)


class BitVecUnsignedDiv(BitVecOperation):
    def __init__(self, a, b, *args, **kwargs):
        super().__init__(a.size, a, b, *args, **kwargs)


class BitVecMod(BitVecOperation):
    def __init__(self, a, b, *args, **kwargs):
        super().__init__(a.size, a, b, *args, **kwargs)


class BitVecRem(BitVecOperation):
    def __init__(self, a, b, *args, **kwargs):
        super().__init__(a.size, a, b, *args, **kwargs)


class BitVecUnsignedRem(BitVecOperation):
    def __init__(self, a, b, *args, **kwargs):
        super().__init__(a.size, a, b, *args, **kwargs)


class BitVecShiftLeft(BitVecOperation):
    def __init__(self, a, b, *args, **kwargs):
        super().__init__(a.size, a, b, *args, **kwargs)


class BitVecShiftRight(BitVecOperation):
    def __init__(self, a, b, *args, **kwargs):
        super().__init__(a.size, a, b, *args, **kwargs)


class BitVecArithmeticShiftLeft(BitVecOperation):
    def __init__(self, a, b, *args, **kwargs):
        super().__init__(a.size, a, b, *args, **kwargs)


class BitVecArithmeticShiftRight(BitVecOperation):
    def __init__(self, a, b, *args, **kwargs):
        super().__init__(a.size, a, b, *args, **kwargs)


class BitVecAnd(BitVecOperation):
    def __init__(self, a, b, *args, **kwargs):
        super().__init__(a.size, a, b, *args, **kwargs)


class BitVecOr(BitVecOperation):
    def __init__(self, a, b, *args, **kwargs):
        assert isinstance(a, BitVec)
        assert isinstance(b, BitVec)
        assert a.size == b.size
        super().__init__(a.size, a, b, *args, **kwargs)


class BitVecXor(BitVecOperation):
    def __init__(self, a, b, *args, **kwargs):
        super().__init__(a.size, a, b, *args, **kwargs)


class BitVecNot(BitVecOperation):
    def __init__(self, a, **kwargs):
        super().__init__(a.size, a, **kwargs)


class BitVecNeg(BitVecOperation):
    def __init__(self, a, *args, **kwargs):
        super().__init__(a.size, a, *args, **kwargs)


# Comparing two bitvectors results in a Bool
class LessThan(BoolOperation):
    def __init__(self, a, b, *args, **kwargs):
        super().__init__(a, b, *args, **kwargs)


class LessOrEqual(BoolOperation):
    def __init__(self, a, b, *args, **kwargs):
        super().__init__(a, b, *args, **kwargs)


class Equal(BoolOperation):
    def __init__(self, a, b, *args, **kwargs):
        assert a.size == b.size
        super().__init__(a, b, *args, **kwargs)


class GreaterThan(BoolOperation):
    def __init__(self, a, b, *args, **kwargs):
        assert a.size == b.size
        super().__init__(a, b, *args, **kwargs)


class GreaterOrEqual(BoolOperation):
    def __init__(self, a, b, *args, **kwargs):
        assert a.size == b.size
        super().__init__(a, b, *args, **kwargs)


class UnsignedLessThan(BoolOperation):
    def __init__(self, a, b, *args, **kwargs):
        super().__init__(a, b, *args, **kwargs)
        assert a.size == b.size


class UnsignedLessOrEqual(BoolOperation):
    def __init__(self, a, b, *args, **kwargs):
        assert a.size == b.size
        super().__init__(a, b, *args, **kwargs)


class UnsignedGreaterThan(BoolOperation):
    def __init__(self, a, b, *args, **kwargs):
        assert a.size == b.size
        super().__init__(a, b, *args, **kwargs)


class UnsignedGreaterOrEqual(BoolOperation):
    def __init__(self, a, b, *args, **kwargs):
        assert a.size == b.size
        super(UnsignedGreaterOrEqual, self).__init__(a, b, *args, **kwargs)


###############################################################################
# Array  BV32 -> BV8  or BV64 -> BV8
class Array(Expression):
    def __init__(self, index_bits, index_max, value_bits, *operands, **kwargs):
        assert index_bits in (32, 64, 256)
        assert value_bits in (8, 16, 32, 64, 256)
        assert index_max is None or isinstance(index_max, int)
        assert index_max is None or index_max >= 0 and index_max < 2 ** index_bits
        self._index_bits = index_bits
        self._index_max = index_max
        self._value_bits = value_bits
        super().__init__(*operands, **kwargs)
        assert type(self) is not Array, "Abstract class"

    def _get_size(self, index):
        start, stop = self._fix_index(index)
        size = stop - start
        if isinstance(size, BitVec):
            from .visitors import simplify

            size = simplify(size)
        else:
            size = BitVecConstant(self.index_bits, size)
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
            arr = ArrayVariable(self.index_bits, len(possible_array), 8)
            for pos, byte in enumerate(possible_array):
                arr = arr.store(pos, byte)
            return arr
        raise ValueError  # cast not implemented

    def cast_index(self, index):
        if isinstance(index, int):
            # assert self.index_max is None or index >= 0 and index < self.index_max
            return BitVecConstant(self.index_bits, index)
        assert isinstance(index, BitVec) and index.size == self.index_bits
        return index

    def cast_value(self, value):
        if isinstance(value, (str, bytes)) and len(value) == 1:
            value = ord(value)
        if isinstance(value, int):
            return BitVecConstant(self.value_bits, value)
        assert isinstance(value, BitVec)
        assert value.size == self.value_bits
        return value

    def __len__(self):
        if self.index_max is None:
            raise Exception("Array max index not set")
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
        return ArraySelect(self, index)

    def store(self, index, value):
        return ArrayStore(self, self.cast_index(index), self.cast_value(value))

    def write(self, offset, buf):
        if not isinstance(buf, (Array, bytearray)):
            raise TypeError("Array or bytearray expected got {:s}".format(type(buf)))
        arr = self
        for i, val in enumerate(buf):
            arr = arr.store(offset + i, val)
        return arr

    def read(self, offset, size):
        return ArraySlice(self, offset, size)

    def __getitem__(self, index):
        if isinstance(index, slice):
            start, stop = self._fix_index(index)
            size = self._get_size(index)
            return ArraySlice(self, start, size)
        else:
            if self.index_max is not None:
                if not isinstance(index, Expression) and index >= self.index_max:
                    raise IndexError
        return self.select(self.cast_index(index))

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
        bytes = []
        for offset in range(size):
            bytes.append(self.get(address + offset, 0))
        return BitVecConcat(size * self.value_bits, *bytes)

    def read_LE(self, address, size):
        address = self.cast_index(address)
        bytes = []
        for offset in range(size):
            bytes.append(self.get(address + offset, 0))
        return BitVecConcat(size * self.value_bits, *reversed(bytes))

    def write_BE(self, address, value, size):
        address = self.cast_index(address)
        value = BitVec(size * self.value_bits).cast(value)
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
        if not isinstance(other, (Array, bytearray)):
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
                "concatenation{}".format(uuid.uuid1()),
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
                "concatenation{}".format(uuid.uuid1()),
            )
        )
        for index in range(len(other)):
            new_arr[index] = simplify(other[index])
        _concrete_cache = new_arr._concrete_cache
        for index in range(self.index_max):
            new_arr[index + len(other)] = simplify(self[index])
        new_arr._concrete_cache.update(_concrete_cache)
        return new_arr


class ArrayVariable(Array, Variable):
    def __init__(self, index_bits, index_max, value_bits, name, *operands, **kwargs):
        super().__init__(index_bits, index_max, value_bits, name, **kwargs)

    @property
    def declaration(self):
        return f"(declare-fun {self.name} () (Array (_ BitVec {self.index_bits}) (_ BitVec {self.value_bits})))"


class ArrayOperation(Array, Operation):
    def __init__(self, array, *operands, **kwargs):
        assert isinstance(array, Array)
        super().__init__(
            array.index_bits, array.index_max, array.value_bits, array, *operands, **kwargs
        )


class ArrayStore(ArrayOperation):
    def __init__(self, array, index, value, *args, **kwargs):
        assert isinstance(array, Array)
        assert isinstance(index, BitVec) and index.size == array.index_bits
        assert isinstance(value, BitVec) and value.size == array.value_bits
        super().__init__(array, index, value, *args, **kwargs)

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


class ArraySlice(Array):
    def __init__(self, array, offset, size, *args, **kwargs):
        if not isinstance(array, Array):
            raise ValueError("Array expected")
        if isinstance(array, ArrayProxy):
            array = array._array
        super().__init__(array.index_bits, array.index_max, array.value_bits, *args, **kwargs)

        self._array = array
        self._slice_offset = offset
        self._slice_size = size

    @property
    def underlying_variable(self):
        return self._array.underlying_variable

    @property
    def operands(self):
        return self._array.operands

    @property
    def index_bits(self):
        return self._array.index_bits

    @property
    def index_max(self):
        return self._slice_size

    @property
    def value_bits(self):
        return self._array.value_bits

    @property
    def taint(self):
        return self._array.taint

    def select(self, index):
        return self._array.select(index + self._slice_offset)

    def store(self, index, value):
        return ArraySlice(
            self._array.store(index + self._slice_offset, value),
            self._slice_offset,
            self._slice_size,
        )


class ArrayProxy(Array):
    def __init__(self, array, default=None):
        assert isinstance(array, Array)
        self._default = default
        self._concrete_cache = {}
        self._written = None
        if isinstance(array, ArrayProxy):
            # copy constructor
            super().__init__(array.index_bits, array.index_max, array.value_bits)
            self._array = array._array
            self._name = array._name
            if default is None:
                self._default = array._default
            self._concrete_cache = dict(array._concrete_cache)
            self._written = set(array.written)
        elif isinstance(array, ArrayVariable):
            # fresh array proxy
            super().__init__(array.index_bits, array.index_max, array.value_bits)
            self._array = array
            self._name = array.name
        else:
            # arrayproxy for a prepopulated array
            super().__init__(array.index_bits, array.index_max, array.value_bits)
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
        return self._array.operands

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
        index = self.cast_index(index)
        if self.index_max is not None:
            from .visitors import simplify

            index = simplify(
                BitVecITE(self.index_bits, index < 0, self.index_max + index + 1, index)
            )
        if isinstance(index, Constant) and index.value in self._concrete_cache:
            return self._concrete_cache[index.value]
        return self._array.select(index)

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
        self.written.add(index)
        self._array = self._array.store(index, value)
        return self

    def __getitem__(self, index):
        if isinstance(index, slice):
            start, stop = self._fix_index(index)
            size = self._get_size(index)
            array_proxy_slice = ArrayProxy(ArraySlice(self, start, size), default=self._default)
            array_proxy_slice._concrete_cache = {}
            for k, v in self._concrete_cache.items():
                if k >= start and k < start + size:
                    array_proxy_slice._concrete_cache[k - start] = v
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
        state["_written"] = self._written
        return state

    def __setstate__(self, state):
        self._default = state["_default"]
        self._array = state["_array"]
        self._name = state["name"]
        self._concrete_cache = state["_concrete_cache"]
        self._written = state["_written"]

    def __copy__(self):
        return ArrayProxy(self)

    @property
    def written(self):
        # Calculate only first time
        if self._written is None:
            written = set()
            # take out Proxy sleve
            array = self._array
            offset = 0
            if isinstance(array, ArraySlice):
                # if it is a proxy over a slice take out the slice too
                offset = array._slice_offset
                array = array._array
            while not isinstance(array, ArrayVariable):
                # The index written to underlaying Array are displaced when sliced
                written.add(array.index - offset)
                array = array.array
            assert isinstance(array, ArrayVariable)
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

    def get(self, index, default=None):
        if default is None:
            default = self._default
        index = self.cast_index(index)
        value = self.select(index)
        if default is None:
            return value

        is_known = self.is_known(index)
        default = self.cast_value(default)
        return BitVecITE(self._array.value_bits, is_known, value, default)


class ArraySelect(BitVec, Operation):
    def __init__(self, array, index, *args, **kwargs):
        assert isinstance(array, Array)
        assert isinstance(index, BitVec) and index.size == array.index_bits
        super().__init__(array.value_bits, array, index, *args, **kwargs)

    @property
    def array(self):
        return self.operands[0]

    @property
    def index(self):
        return self.operands[1]

    def __repr__(self):
        return f"<ArraySelect obj with index={self.index}:\n{self.array}>"


class BitVecSignExtend(BitVecOperation):
    def __init__(self, operand, size_dest, *args, **kwargs):
        assert isinstance(operand, BitVec)
        assert isinstance(size_dest, int)
        assert size_dest >= operand.size
        super().__init__(size_dest, operand, *args, **kwargs)
        self.extend = size_dest - operand.size


class BitVecZeroExtend(BitVecOperation):
    def __init__(self, size_dest, operand, *args, **kwargs):
        assert isinstance(operand, BitVec)
        assert isinstance(size_dest, int)
        assert size_dest >= operand.size
        super().__init__(size_dest, operand, *args, **kwargs)
        self.extend = size_dest - operand.size


class BitVecExtract(BitVecOperation):
    def __init__(self, operand, offset, size, *args, **kwargs):
        assert isinstance(offset, int)
        assert isinstance(size, int)
        assert offset >= 0 and offset + size <= operand.size
        super().__init__(size, operand, *args, **kwargs)
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
    def __init__(self, size_dest, *operands, **kwargs):
        assert isinstance(size_dest, int)
        assert all(isinstance(x, BitVec) for x in operands)
        assert size_dest == sum(x.size for x in operands)
        super().__init__(size_dest, *operands, **kwargs)


class BitVecITE(BitVecOperation):
    def __init__(self, size, condition, true_value, false_value, *args, **kwargs):
        assert isinstance(true_value, BitVec)
        assert isinstance(false_value, BitVec)
        assert true_value.size == size
        assert false_value.size == size
        super().__init__(size, condition, true_value, false_value, *args, **kwargs)
