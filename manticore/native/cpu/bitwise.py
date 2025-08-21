#!/usr/bin/env python

from ...core.smtlib import Operators
from ...core.smtlib.expression import BitVec


def Mask(width):
    """
    Return a mask with the low `width` bits set.

    :param int width: How many bits to set to 1
    :return: int or long
    """
    return (1 << width) - 1


def Bit(value, idx):
    """
    Extract `idx` bit from `value`.

    :param value: Source value from which to extract.
    :type value: int or long or BitVec
    :param idx: Bit index
    :return: int or long or BitVex
    """
    return Operators.EXTRACT(value, idx, 1)


def GetNBits(value, nbits):
    """
    Get the first `nbits` from `value`.

    :param value: Source value from which to extract
    :type value: int or long or BitVec
    :param int nbits: How many bits to extract
    :return: Low `nbits` bits of `value`.
    :rtype int or long or BitVec
    """
    # NOP if sizes are the same
    if isinstance(value, int):
        return Operators.EXTRACT(value, 0, nbits)
    elif isinstance(value, BitVec):
        if value.size < nbits:
            return Operators.ZEXTEND(value, nbits)
        else:
            return Operators.EXTRACT(value, 0, nbits)


def SInt(value, width):
    """
    Convert a bitstring `value` of `width` bits to a signed integer
    representation.

    :param value: The value to convert.
    :type value: int or long or BitVec
    :param int width: The width of the bitstring to consider
    :return: The converted value
    :rtype int or long or BitVec
    """
    return Operators.ITEBV(
        width,
        Bit(value, width - 1) == 1,
        GetNBits(value, width) - 2**width,
        GetNBits(value, width),
    )


def UInt(value, width):
    """
    Return integer value of `value` as a bitstring of `width` width.

    :param value: The value to convert.
    :type value: int or long or BitVec
    :param int width: The width of the bitstring to consider
    :return: The integer value
    :rtype int or long or BitVec
    """
    return GetNBits(value, width)


def LSL_C(value, amount, width, with_carry=True):
    """
    The ARM LSL_C (logical left shift with carry) operation.

    :param value: Value to shift
    :type value: int or long or BitVec
    :param int amount: How many bits to shift it.
    :param int width: Width of the value
    :return: Resultant value and the carry result
    :rtype tuple
    """
    if isinstance(amount, int):
        assert amount > 0
    value = Operators.ZEXTEND(value, width * 2)
    amount = Operators.ZEXTEND(amount, width * 2)
    shifted = value << amount
    result = GetNBits(shifted, width)
    if with_carry:
        carry = Bit(shifted, width)
        return (result, carry)
    else:
        return result


def LSL(value, amount, width):
    """
    The ARM LSL (logical left shift) operation.

    :param value: Value to shift
    :type value: int or long or BitVec
    :param int amount: How many bits to shift it.
    :param int width: Width of the value
    :return: Resultant value
    :rtype int or BitVec
    """
    if isinstance(amount, int) and amount == 0:
        return value

    result = LSL_C(value, amount, width, with_carry=False)
    return result


def LSR_C(value, amount, width, with_carry=True):
    """
    The ARM LSR_C (logical shift right with carry) operation.

    :param value: Value to shift
    :type value: int or long or BitVec
    :param int amount: How many bits to shift it.
    :param int width: Width of the value
    :return: Resultant value and carry result
    :rtype tuple
    """
    if isinstance(amount, int):
        assert amount > 0
    result = GetNBits(value >> amount, width)
    if with_carry:
        carry = Bit(value >> (amount - 1), 0)
        return (result, carry)
    else:
        return result


def LSR(value, amount, width):
    """
    The ARM LSR (logical shift right) operation.

    :param value: Value to shift
    :type value: int or long or BitVec
    :param int amount: How many bits to shift it.
    :param int width: Width of the value
    :return: Resultant value
    :rtype int or BitVec
    """
    if isinstance(amount, int) and amount == 0:
        return value
    result = LSR_C(value, amount, width, with_carry=False)
    return result


def ASR_C(value, amount, width, with_carry=True):
    """
    The ARM ASR_C (arithmetic shift right with carry) operation.

    :param value: Value to shift
    :type value: int or long or BitVec
    :param int amount: How many bits to shift it.
    :param int width: Width of the value
    :return: Resultant value and carry result
    :rtype tuple
    """
    if isinstance(amount, int) and isinstance(width, int):
        assert amount <= width
    if isinstance(amount, int):
        assert amount > 0
    if isinstance(amount, int) and isinstance(width, int):
        assert amount + width <= width * 2
    value = Operators.SEXTEND(value, width, width * 2)
    amount = Operators.ZEXTEND(amount, width * 2)
    result = GetNBits(value >> amount, width)
    if with_carry:
        carry = Bit(value, amount - 1)
        return (result, carry)
    else:
        return result


def ASR(value, amount, width):
    """
    The ARM ASR (arithmetic shift right) operation.

    :param value: Value to shift
    :type value: int or long or BitVec
    :param int amount: How many bits to shift it.
    :param int width: Width of the value
    :return: Resultant value
    :rtype int or BitVec
    """
    if isinstance(amount, int) and amount == 0:
        return value

    result = ASR_C(value, amount, width, with_carry=False)
    return result


def ROR_C(value, amount, width, with_carry=True):
    """
    The ARM ROR_C (rotate right with carry) operation.

    :param value: Value to shift
    :type value: int or long or BitVec
    :param int amount: How many bits to rotate it.
    :param int width: Width of the value
    :return: Resultant value and carry result
    :rtype tuple
    """
    if isinstance(amount, int) and isinstance(width, int):
        assert amount <= width
    if isinstance(amount, int):
        assert amount > 0
    m = amount % width
    right, _ = LSR_C(value, m, width)
    left, _ = LSL_C(value, width - m, width)
    result = left | right
    if with_carry:
        carry = Bit(result, width - 1)
        return (result, carry)
    else:
        return result


def ROR(value, amount, width):
    """
    The ARM ROR (rotate right) operation.

    :param value: Value to shift
    :type value: int or long or BitVec
    :param int amount: How many bits to rotate it.
    :param int width: Width of the value
    :return: Resultant value
    :rtype int or BitVec
    """
    if isinstance(amount, int) and amount == 0:
        return value
    result = ROR_C(value, amount, width, with_carry=False)
    return result


def RRX_C(value, carry, width, with_carry=True):
    """
    The ARM RRX (rotate right with extend and with carry) operation.

    :param value: Value to shift
    :type value: int or long or BitVec
    :param int amount: How many bits to rotate it.
    :param int width: Width of the value
    :return: Resultant value and carry result
    :rtype tuple
    """
    result = (value >> 1) | (carry << (width - 1))
    if with_carry:
        carry_out = Bit(value, 0)
        return (result, carry_out)
    else:
        return result


def RRX(value, carry, width):
    """
    The ARM RRX (rotate right with extend) operation.

    :param value: Value to shift
    :type value: int or long or BitVec
    :param int amount: How many bits to rotate it.
    :param int width: Width of the value
    :return: Resultant value
    :rtype int or BitVec
    """
    result = RRX_C(value, carry, width, with_carry=False)
    return result
