from .expression import (
    BitVec,
    BitVecExtract,
    BitVecSignExtend,
    BitVecZeroExtend,
    BitVecConstant,
    BitVecConcat,
    Bool,
    BitVecITE,
    BoolConstant,
    BoolITE,
)
from . import issymbolic
import math


def ORD(s):
    if isinstance(s, BitVec):
        if s.size == 8:
            return s
        else:
            return BitVecExtract(s, 0, 8)
    elif isinstance(s, int):
        return s & 0xFF
    else:
        return ord(s)


def CHR(s):
    if isinstance(s, BitVec):
        if s.size == 8:
            return s
        else:
            return BitVecExtract(s, 0, 8)
    elif isinstance(s, int):
        return bytes([s & 0xFF])
    else:
        assert len(s) == 1
        return s


def NOT(a):
    if isinstance(a, bool):
        return not a
    if isinstance(a, (Bool, int)):
        return ~a
    return a == False


def AND(a, b, *others):
    if len(others) > 0:
        b = AND(b, others[0], *others[1:])
    if isinstance(a, Bool):
        return a & b
    if isinstance(b, Bool):
        return b & a
    assert isinstance(a, bool) and isinstance(b, bool)
    return a & b


def OR(a, b, *others):
    if len(others) > 0:
        b = OR(b, others[0], *others[1:])
    if isinstance(a, Bool):
        return a | b
    if isinstance(b, Bool):
        return b | a
    result = a | b
    if isinstance(result, (BitVec, int)):
        result = ITE(result != 0, True, False)
    return result


def UGT(a, b):
    if isinstance(a, BitVec):
        return a.ugt(b)
    if isinstance(b, BitVec):
        return b.ult(a)
    if a < 0:
        a = a & 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF
    if b < 0:
        b = b & 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF

    return a > b


def UGE(a, b):
    if isinstance(a, BitVec):
        return a.uge(b)
    if isinstance(b, BitVec):
        return b.ule(a)
    if a < 0:
        a = a & 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF
    if b < 0:
        b = b & 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF

    return a >= b


def ULT(a, b):
    if isinstance(a, BitVec):
        return a.ult(b)
    if isinstance(b, BitVec):
        return b.ugt(a)
    if a < 0:
        a = a & 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF
    if b < 0:
        b = b & 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF

    return a < b


def ULE(a, b):
    if isinstance(a, BitVec):
        return a.ule(b)
    if isinstance(b, BitVec):
        return b.uge(a)
    if a < 0:
        a = a & 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF
    if b < 0:
        b = b & 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF

    return a <= b


def EXTRACT(x, offset, size):
    if isinstance(x, BitVec) and isinstance(offset, BitVec):
        return BitVecExtract(x >> offset, 0, size)
    elif isinstance(x, BitVec):
        if offset == 0 and size == x.size:
            return x
        return BitVecExtract(x, offset, size)
    else:
        return (x >> offset) & ((1 << size) - 1)


def SEXTEND(x, size_src, size_dest):
    if isinstance(x, int):
        if x >= (1 << (size_src - 1)):
            x -= 1 << size_src
        return x & ((1 << size_dest) - 1)
    assert x.size == size_src
    return BitVecSignExtend(x, size_dest)


def ZEXTEND(x, size):
    if isinstance(x, int):
        return x & ((1 << size) - 1)
    assert isinstance(x, BitVec) and size - x.size >= 0
    if size - x.size > 0:
        return BitVecZeroExtend(size, x)
    else:
        return x


def CONCAT(total_size, *args):
    arg_size = total_size // len(args)
    if any(issymbolic(x) for x in args):
        if len(args) > 1:

            def cast(x):
                if isinstance(x, int):
                    return BitVecConstant(arg_size, x)
                return x

            return BitVecConcat(total_size, *list(map(cast, args)))
        else:
            return args[0]
    else:
        result = 0
        for arg in args:
            result = (result << arg_size) | (arg & ((1 << arg_size) - 1))
        return result


def ITE(cond, true_value, false_value):
    assert isinstance(true_value, (Bool, bool, BitVec, int))
    assert isinstance(false_value, (Bool, bool, BitVec, int))
    assert isinstance(cond, (Bool, bool))
    if isinstance(cond, bool):
        if cond:
            return true_value
        else:
            return false_value

    if isinstance(true_value, bool):
        true_value = BoolConstant(true_value)

    if isinstance(false_value, bool):
        false_value = BoolConstant(false_value)

    return BoolITE(cond, true_value, false_value)


def ITEBV(size, cond, true_value, false_value):
    if isinstance(cond, BitVec):
        cond = cond.Bool()
    if isinstance(cond, int):
        cond = cond != 0

    assert isinstance(cond, (Bool, bool))
    assert isinstance(true_value, (BitVec, int))
    assert isinstance(false_value, (BitVec, int))
    assert isinstance(size, int)

    if isinstance(cond, BoolConstant) and not cond.taint:
        cond = cond.value

    if isinstance(cond, bool):
        if cond:
            return true_value
        else:
            return false_value

    if isinstance(true_value, int):
        true_value = BitVecConstant(size, true_value)

    if isinstance(false_value, int):
        false_value = BitVecConstant(size, false_value)
    return BitVecITE(size, cond, true_value, false_value)


def UDIV(dividend, divisor):
    if isinstance(dividend, BitVec):
        return dividend.udiv(divisor)
    elif isinstance(divisor, BitVec):
        return divisor.rudiv(dividend)
    assert dividend >= 0 or divisor > 0  # unsigned-es
    return dividend // divisor


def SDIV(a, b):
    if isinstance(a, BitVec):
        return a.sdiv(b)
    elif isinstance(b, BitVec):
        return b.rsdiv(a)
    return int(math.trunc(float(a) / float(b)))


def SMOD(a, b):
    if isinstance(a, BitVec):
        return a.smod(b)
    elif isinstance(b, BitVec):
        return b.rsmod(a)
    return int(math.fmod(a, b))


def SREM(a, b):
    if isinstance(a, BitVec):
        return a.srem(b)
    elif isinstance(b, BitVec):
        return b.rsrem(a)
    elif isinstance(a, int) and isinstance(b, int):
        return a - int(a / b) * b
    return a % b


def UREM(a, b):
    if isinstance(a, BitVec):
        return a.urem(b)
    elif isinstance(b, BitVec):
        return b.rurem(a)
    return a % b


def SAR(size, a, b):
    assert isinstance(size, int)
    if isinstance(b, BitVec) and b.size != size:
        b = ZEXTEND(b, size)
    if isinstance(a, BitVec):
        assert size == a.size
        return a.sar(b)
    elif isinstance(b, BitVec):
        return BitVecConstant(size, a).sar(b)
    else:
        tempDest = a
        tempCount = b
        sign = tempDest & (1 << (size - 1))
        while tempCount != 0:
            tempDest = (tempDest >> 1) | sign
            tempCount = tempCount - 1
        return tempDest


def ABS(a):
    if issymbolic(a):
        return ITEBV(a.size, a < 0, -a, a)
    else:
        return abs(a)
