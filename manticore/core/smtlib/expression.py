import operator
import weakref

class Expression(object):
    ''' Abstract taintable Expression. '''
    def __init__(self, taint=()):
        if self.__class__ is Expression:
            raise TypeError
        assert isinstance(taint, (tuple, frozenset))
        super(Expression, self).__init__()
        self._taint = frozenset(taint)

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
        assert isinstance(name, str) and ' ' not in name
        super(Variable, self).__init__(*args, **kwargs)
        self._name = name

    @property
    def declaration(self):
        pass

    @property
    def name(self):
        return self._name


class Constant(Expression):
    def __init__(self, value, *args, **kwargs):
        if self.__class__ is Constant:
            raise TypeError
        assert isinstance(value, (bool, int, long))
        super(Constant, self).__init__(*args, **kwargs)
        self._value = value

    @property
    def value(self):
        return self._value


class Operation(Expression):
    def __init__(self, *operands, **kwargs):
        if self.__class__ is Operation:
            raise TypeError
        assert len(operands) > 0
        assert all(isinstance(x, Expression) for x in operands)
        self._operands = operands

        # If taint was not forced by a keyword argument calculate default
        if 'taint' not in kwargs:
            kwargs['taint'] = reduce(lambda x, y: x.union(y.taint), operands, frozenset())

        super(Operation, self).__init__(**kwargs)

    @property
    def operands(self):
        return self._operands


###############################################################################
# Booleans
class Bool(Expression):
    def __init__(self, *operands, **kwargs):
        super(Bool, self).__init__(*operands, **kwargs)

    def cast(self, value, **kwargs):
        if isinstance(value, Bool):
            return value
        assert isinstance(value, (int, long, bool))
        return BoolConstant(bool(value), **kwargs)

    def __cmp__(self, *args):
        raise NotImplementedError("CMP for Bool")

    def __invert__(self):
        return BoolNot(self)

    def __eq__(self, other):
        return BoolEq(self, self.cast(other))

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

    def __nonzero__(self):
        raise NotImplementedError("__nonzero__ for Bool")

class BoolVariable(Bool, Variable):
    def __init__(self, name, *args, **kwargs):
        super(BoolVariable, self).__init__(name, *args, **kwargs)

    @property
    def declaration(self):
        return '(declare-fun %s () Bool)' % self.name


class BoolConstant(Bool, Constant):
    def __init__(self, value, *args, **kwargs):
        assert isinstance(value, bool)
        super(BoolConstant, self).__init__(value, *args, **kwargs)

    def __nonzero__(self):
        return self.value


class BoolOperation(Operation, Bool):
    def __init__(self, *operands, **kwargs):
        super(BoolOperation, self).__init__(*operands, **kwargs)


class BoolNot(BoolOperation):
    def __init__(self, value, **kwargs):
        super(BoolNot, self).__init__(value, **kwargs)


class BoolEq(BoolOperation):
    def __init__(self, a, b, **kwargs):
        super(BoolEq, self).__init__(a, b, **kwargs)


class BoolAnd(BoolOperation):
    def __init__(self, a, b, **kwargs):
        super(BoolAnd, self).__init__(a, b, **kwargs)


class BoolOr(BoolOperation):
    def __init__(self, a, b, **kwargs):
        assert isinstance(a, Bool)
        assert isinstance(b, Bool)
        super(BoolOr, self).__init__(a, b, **kwargs)


class BoolXor(BoolOperation):
    def __init__(self, a, b, **kwargs):
        super(BoolXor, self).__init__(a, b, **kwargs)


class BoolITE(BoolOperation):
    def __init__(self, cond, true, false, **kwargs):
        assert isinstance(true, Bool)
        assert isinstance(false, Bool)
        assert isinstance(cond, Bool)
        super(BoolITE, self).__init__(cond, true, false, **kwargs)


class BitVec(Expression):
    ''' This adds a bitsize to the Expression class '''
    def __init__(self, size, *operands, **kwargs):
        #assert size in (1, 8, 16, 32, 64, 128, 256)
        super(BitVec, self).__init__(*operands, **kwargs)
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
        if isinstance(value, str) and len(value) == 1:
            value = ord(value)
        assert isinstance(value, (int, long, bool))
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
        super(BitVecVariable, self).__init__(*args, **kwargs)

    @property
    def declaration(self):
        return '(declare-fun %s () (_ BitVec %d))' % (self.name, self.size)


class BitVecConstant(BitVec, Constant):
    def __init__(self, size, value, *args, **kwargs):
        assert isinstance(value, (int, long))
        super(BitVecConstant, self).__init__(size, value, *args, **kwargs)

    def __nonzero__(self):
        return self.value != 0


class BitVecOperation(BitVec, Operation):
    def __init__(self, size, *operands, **kwargs):
        #assert all(x.size == size for x in operands)
        super(BitVecOperation, self).__init__(size, *operands, **kwargs)


class BitVecAdd(BitVecOperation):
    def __init__(self, a, b, *args, **kwargs):
        super(BitVecAdd, self).__init__(a.size, a, b, *args, **kwargs)


class BitVecSub(BitVecOperation):
    def __init__(self, a, b, *args, **kwargs):
        super(BitVecSub, self).__init__(a.size, a, b, *args, **kwargs)


class BitVecMul(BitVecOperation):
    def __init__(self, a, b, *args, **kwargs):
        super(BitVecMul, self).__init__(a.size, a, b, *args, **kwargs)


class BitVecDiv(BitVecOperation):
    def __init__(self, a, b, *args, **kwargs):
        super(BitVecDiv, self).__init__(a.size, a, b, *args, **kwargs)


class BitVecUnsignedDiv(BitVecOperation):
    def __init__(self, a, b, *args, **kwargs):
        super(BitVecUnsignedDiv, self).__init__(a.size, a, b, *args, **kwargs)


class BitVecMod(BitVecOperation):
    def __init__(self, a, b, *args, **kwargs):
        super(BitVecMod, self).__init__(a.size, a, b, *args, **kwargs)

class BitVecRem(BitVecOperation):
    def __init__(self, a, b, *args, **kwargs):
        super(BitVecRem, self).__init__(a.size, a, b, *args, **kwargs)

class BitVecUnsignedRem(BitVecOperation):
    def __init__(self, a, b, *args, **kwargs):
        super(BitVecUnsignedRem, self).__init__(a.size, a, b, *args, **kwargs)


class BitVecShiftLeft(BitVecOperation):
    def __init__(self, a, b, *args, **kwargs):
        super(BitVecShiftLeft, self).__init__(a.size, a, b, *args, **kwargs)


class BitVecShiftRight(BitVecOperation):
    def __init__(self, a, b, *args, **kwargs):
        super(BitVecShiftRight, self).__init__(a.size, a, b, *args, **kwargs)


class BitVecArithmeticShiftLeft(BitVecOperation):
    def __init__(self, a, b, *args, **kwargs):
        super(self.__class__, self).__init__(a.size, a, b, *args, **kwargs)


class BitVecArithmeticShiftRight(BitVecOperation):
    def __init__(self, a, b, *args, **kwargs):
        super(self.__class__, self).__init__(a.size, a, b, *args, **kwargs)


class BitVecAnd(BitVecOperation):
    def __init__(self, a, b, *args, **kwargs):
        super(BitVecAnd, self).__init__(a.size, a, b, *args, **kwargs)


class BitVecOr(BitVecOperation):
    def __init__(self, a, b, *args, **kwargs):
        assert isinstance(a, BitVec)
        assert isinstance(b, BitVec)
        assert a.size == b.size
        super(BitVecOr, self).__init__(a.size, a, b, *args, **kwargs)


class BitVecXor(BitVecOperation):
    def __init__(self, a, b, *args, **kwargs):
        super(BitVecXor, self).__init__(a.size, a, b, *args, **kwargs)


class BitVecNot(BitVecOperation):
    def __init__(self, a, **kwargs):
        super(BitVecNot, self).__init__(a.size, a, **kwargs)


class BitVecNeg(BitVecOperation):
    def __init__(self, a, *args, **kwargs):
        super(BitVecNeg, self).__init__(a.size, a, *args, **kwargs)


# Comparing two bitvectors results in a Bool
class LessThan(BoolOperation):
    def __init__(self, a, b, *args, **kwargs):
        super(LessThan, self).__init__(a, b, *args, **kwargs)


class LessOrEqual(BoolOperation):
    def __init__(self, a, b, *args, **kwargs):
        super(LessOrEqual, self).__init__(a, b, *args, **kwargs)


class Equal(BoolOperation):
    def __init__(self, a, b, *args, **kwargs):
        assert a.size == b.size
        super(Equal, self).__init__(a, b, *args, **kwargs)


class GreaterThan(BoolOperation):
    def __init__(self, a, b, *args, **kwargs):
        assert a.size == b.size
        super(GreaterThan, self).__init__(a, b, *args, **kwargs)


class GreaterOrEqual(BoolOperation):
    def __init__(self, a, b, *args, **kwargs):
        assert a.size == b.size
        super(GreaterOrEqual, self).__init__(a, b, *args, **kwargs)


class UnsignedLessThan(BoolOperation):
    def __init__(self, a, b, *args, **kwargs):
        super(UnsignedLessThan, self).__init__(a, b, *args, **kwargs)
        assert a.size == b.size


class UnsignedLessOrEqual(BoolOperation):
    def __init__(self, a, b, *args, **kwargs):
        assert a.size == b.size
        super(UnsignedLessOrEqual, self).__init__(a, b, *args, **kwargs)


class UnsignedGreaterThan(BoolOperation):
    def __init__(self, a, b, *args, **kwargs):
        assert a.size == b.size
        super(UnsignedGreaterThan, self).__init__(a, b, *args, **kwargs)


class UnsignedGreaterOrEqual(BoolOperation):
    def __init__(self, a, b, *args, **kwargs):
        assert a.size == b.size
        super(UnsignedGreaterOrEqual,
              self).__init__(a, b, *args, **kwargs)


###############################################################################
# Array  BV32 -> BV8  or BV64 -> BV8
class Array(Expression):
    def __init__(self, index_bits, index_max, *operands, **kwargs):
        assert index_bits in (32, 64)
        assert index_max is None or isinstance(index_max, int)
        assert index_max is None or index_max > 0 and index_max < 2 ** index_bits
        self._index_bits = index_bits
        self._index_max = index_max
        super(Array, self).__init__(*operands, **kwargs)

    def cast_index(self, index):
        if isinstance(index, (int, long)):
            assert self.index_max is None or index >= 0 and index < self.index_max
            return BitVecConstant(self._index_bits, index)
        assert isinstance(index, BitVec) and index.size == self._index_bits
        return index

    def cast_value(self, value):
        if isinstance(value, str) and len(value) == 1:
            value = ord(value)
        if isinstance(value, (int, long)):
            return BitVecConstant(8, value)
        assert isinstance(value, BitVec) and value.size == 8
        return value

    @property
    def index_bits(self):
        return self._index_bits

    @property
    def index_max(self):
        return self._index_max

    def select(self, index):
        return ArraySelect(self, self.cast_index(index))

    def store(self, index, value):
        return ArrayStore(self, self.cast_index(index), self.cast_value(value))


class ArrayVariable(Array, Variable):
    def __init__(self, index_bits, index_max, name, *operands, **kwargs):
        super(ArrayVariable, self).__init__(index_bits, index_max, name, **kwargs)

    @property
    def declaration(self):
        return '(declare-fun %s () (Array (_ BitVec %d) (_ BitVec 8)))' % (self.name, self.index_bits)

    def __getitem__(self, index):
        return ArraySelect(self, self.cast_index(index))


class ArrayOperation(Array, Operation):
    def __init__(self, array, *operands, **kwargs):
        assert isinstance(array, Array)
        super(ArrayOperation, self).__init__(array.index_bits, array.index_max, array, *operands, **kwargs)


class ArrayStore(ArrayOperation):
    def __init__(self, array, index, value, *args, **kwargs):
        assert isinstance(array, Array)
        assert isinstance(index, BitVec) and index.size == array.index_bits
        assert isinstance(value, BitVec) and value.size == 8
        super(ArrayStore, self).__init__(array, index, value, *args, **kwargs)

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
    def byte(self):
        return self.operands[2]

class ArrayProxy(ArrayVariable):
    def __init__(self, array):
        assert isinstance(array, ArrayVariable)
        super(ArrayProxy, self).__init__(array.index_bits, array.index_max, array.name)
        self._array = array

    @property
    def operands(self):
        return self._array.operands

    def select(self, index):
        return self._array.select(index)

    def store(self, index, value):
        auxiliar = self._array.store(index, value)
        self._array.store = None
        self._array.select = None
        self._array = auxiliar
        return auxiliar

    def _get_size(self, index):
        size = index.stop - index.start
        if isinstance(size, BitVec):
            import visitors
            size = visitors.ArithmeticSimplifier(expression=size)
        else:
            size = BitVecConstant(self._array.index_bits, size)
        assert isinstance(size, BitVecConstant)
        return size.value

    def __getitem__(self, index):
        if isinstance(index, slice):
            size = self._get_size(index)
            return [self._array.select(index.start+i) for i in xrange(size)]
        else:
            return self._array.select(index)

    def __setitem__(self, index, value):
        if isinstance(index, slice):
            size = self._get_size(index)
            assert len(value) == size
            for i in xrange(size):
                self.store(index.start+i, value[i])
        else:
            self.store(index, value)

    def __len__(self):
        if self._array.index_max is None:
            raise Exception()
        return self._array.index_max


class ArraySelect(BitVec, Operation):
    def __init__(self, array, index, *args, **kwargs):
        assert isinstance(array, Array)
        assert isinstance(index, BitVec) and index.size == array.index_bits
        super(ArraySelect, self).__init__(8, array, index, *args, **kwargs)

    @property
    def array(self):
        return self.operands[0]

    @property
    def index(self):
        return self.operands[1]


class BitVecSignExtend(BitVecOperation):
    def __init__(self, operand, size_dest, *args, **kwargs):
        assert isinstance(operand, BitVec)
        assert isinstance(size_dest, int)
        assert size_dest >= operand.size
        super(BitVecSignExtend, self).__init__(size_dest, operand, *args, **kwargs)
        self.extend = size_dest - operand.size


class BitVecZeroExtend(BitVecOperation):
    def __init__(self, size_dest, operand, *args, **kwargs):
        assert isinstance(operand, BitVec)
        assert isinstance(size_dest, (int, long))
        assert size_dest >= operand.size
        super(BitVecZeroExtend, self).__init__(size_dest, operand, *args, **kwargs)
        self.extend = size_dest-operand.size


class BitVecExtract(BitVecOperation):
    def __init__(self, operand, offset, size, *args, **kwargs):
        assert isinstance(offset, (int, long))
        assert isinstance(size, (int, long))
        assert offset >= 0 and offset + size <= operand.size
        super(BitVecExtract, self).__init__(size, operand, *args, **kwargs)
        self.begining = offset
        self.end = offset + size - 1


class BitVecConcat(BitVecOperation):
    def __init__(self, size_dest, *operands, **kwargs):
        assert isinstance(size_dest, int)
        assert all(map(lambda x: isinstance(x, BitVec), operands))
        assert size_dest == sum(map(lambda x: x.size, operands))
        super(BitVecConcat, self).__init__(size_dest, *operands, **kwargs)


class BitVecITE(BitVecOperation):
    def __init__(self, size, condition, true_value, false_value, *args, **kwargs):
        assert isinstance(true_value, BitVec)
        assert isinstance(false_value, BitVec)
        assert true_value.size == false_value.size
        super(BitVecITE, self).__init__(size, condition, true_value, false_value, *args, **kwargs)  

