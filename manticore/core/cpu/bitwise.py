#!/usr/bin/env python

from core.smtlib import Operators
from core.smtlib.expression import BitVec

def Mask(width):
    return (1 << width) - 1

def Bit(value, idx):
    return Operators.EXTRACT(value, idx, 1)

def GetNBits(value, nbits):
    # NOP if sizes are the same
    if isinstance(value, (int, long)):
        return Operators.EXTRACT(value, 0, nbits)
    elif isinstance(value, BitVec):
        if value.size < nbits:
            return Operators.ZEXTEND(value, nbits)
        else:
            return Operators.EXTRACT(value, 0, nbits)

def SInt(value, width):
    return Operators.ITEBV(width, Bit(value, width-1) == 1,
                                      GetNBits(value, width) - 2**width,
                                      GetNBits(value, width))

def UInt(value, width):
    return GetNBits(value, width)

def LSL_C(value, amount, width):
    assert amount <= width
    assert amount > 0
    result = GetNBits(value << amount, width)
    carry = Bit(value, width - amount)
    return (result, carry)

def LSL(value, amount, width):
    if amount == 0:
        return value

    result, _ = LSL_C(value, amount, width)
    return result

def LSR_C(value, amount, width):
    assert amount <= width
    assert amount > 0
    result = GetNBits(value >> amount, width)
    carry = Bit(value >> (amount - 1), 0)
    return (result, carry)

def LSR(value, amount, width):
    if amount == 0:
        return value
    result, _ = LSR_C(value, amount, width)
    return result

def ASR_C(value, amount, width):
    assert amount <= width
    assert amount > 0
    assert amount + width <= width * 2
    value = Operators.SEXTEND(value, width, width * 2)
    result = GetNBits(value >>  amount     , width) 
    carry =  Bit(value, amount - 1)
    return (result, carry)

def ASR(value, amount, width):
    if amount == 0:
        return value

    result, _ = ASR_C(value, amount, width)
    return result

def ROR_C(value, amount, width):
    assert amount <= width
    assert amount > 0
    m = amount % width
    right, _ = LSR_C(value, m, width)
    left, _ = LSL_C(value, width - m, width)
    result = left | right
    carry = Bit(result, width - 1)
    return (result, carry)

def ROR(value, amount, width):
    if amount == 0:
        return value
    result, _ = ROR_C(value, amount, width)
    return result

def RRX_C(value, carry, width):
    carry_out = Bit(value, 0)
    result = (value >> 1) | (carry << (width-1))
    return (result, carry_out)

def RRX(value, carry, width):
    result, _ = RRX_C(value, carry, width)
    return result

