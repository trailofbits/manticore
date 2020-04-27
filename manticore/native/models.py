"""
Models here are intended to be passed to :meth:`~manticore.native.state.State.invoke_model`, not invoked directly.
"""

from .cpu.abstractcpu import ConcretizeArgument
from .state import State
from ..core.smtlib import issymbolic, Expression
from ..core.smtlib.solver import Z3Solver
from ..core.smtlib.operators import ITEBV, ZEXTEND
from typing import Union

VARIADIC_FUNC_ATTR = "_variadic"


def isvariadic(model):
    """
    :param callable model: Function model
    :return: Whether `model` models a variadic function
    :rtype: bool
    """
    return getattr(model, VARIADIC_FUNC_ATTR, False)


def variadic(func):
    """
    A decorator used to mark a function model as variadic. This function should
    take two parameters: a :class:`~manticore.native.state.State` object, and
    a generator object for the arguments.

    :param callable func: Function model
    """
    setattr(func, VARIADIC_FUNC_ATTR, True)
    return func


def _find_zero(cpu, constrs, ptr):
    """
    Helper for finding the closest NULL or, effectively NULL byte from a starting address.

    :param Cpu cpu:
    :param ConstraintSet constrs: Constraints for current `State`
    :param int ptr: Address to start searching for a zero from
    :return: Offset from `ptr` to first byte that is 0 or an `Expression` that must be zero
    """

    offset = 0
    while True:
        byt = cpu.read_int(ptr + offset, 8)

        if issymbolic(byt):
            if not Z3Solver.instance().can_be_true(constrs, byt != 0):
                break
        else:
            if byt == 0:
                break

        offset += 1

    return offset


def _find_zeros(cpu, constrs, ptr):
    """
    Helper for finding the closest NULL or, effectively NULL byte from a starting address.

    :param Cpu cpu:
    :param ConstraintSet constrs: Constraints for current `State`
    :param int ptr: Address to start searching for a zero from
    :return: Offset from `ptr` to first byte that is 0 or an `Expression` that must be zero
    """

    offset = 0
    zeros = []
    while True:
        byt = cpu.read_int(ptr + offset, 8)

        if issymbolic(byt):
            if Z3Solver.instance().can_be_true(constrs, byt == 0):
                zeros.append(offset)
            if not Z3Solver.instance().can_be_true(constrs, byt != 0):
                break
        else:
            if byt == 0:
                zeros.append(offset)
                break

        offset += 1

    return zeros


def strcmp(state: State, s1: Union[int, Expression], s2: Union[int, Expression]):
    """
    strcmp symbolic model.

    Algorithm: Walks from end of string (minimum offset to NULL in either string)
    to beginning building tree of ITEs each time either of the
    bytes at current offset is symbolic.

    Points of Interest:
    - We've been building up a symbolic tree but then encounter two
    concrete bytes that differ. We can throw away the entire symbolic
    tree!
    - If we've been encountering concrete bytes that match
    at the end of the string as we walk forward, and then we encounter
    a pair where one is symbolic, we can forget about that 0 `ret` we've
    been tracking and just replace it with the symbolic subtraction of
    the two

    :param State state: Current program state
    :param int s1: Address of string 1
    :param int s2: Address of string 2
    :return: Symbolic strcmp result
    :rtype: Expression or int
    """

    cpu = state.cpu

    if issymbolic(s1):
        raise ConcretizeArgument(state.cpu, 1)
    if issymbolic(s2):
        raise ConcretizeArgument(state.cpu, 2)

    s1_zero_idx = _find_zero(cpu, state.constraints, s1)
    s2_zero_idx = _find_zero(cpu, state.constraints, s2)
    min_zero_idx = min(s1_zero_idx, s2_zero_idx)

    ret = None

    for offset in range(min_zero_idx, -1, -1):
        s1char = ZEXTEND(cpu.read_int(s1 + offset, 8), cpu.address_bit_size)
        s2char = ZEXTEND(cpu.read_int(s2 + offset, 8), cpu.address_bit_size)

        if issymbolic(s1char) or issymbolic(s2char):
            if ret is None or (not issymbolic(ret) and ret == 0):
                ret = s1char - s2char
            else:
                ret = ITEBV(cpu.address_bit_size, s1char != s2char, s1char - s2char, ret)
        else:
            if s1char != s2char:
                ret = s1char - s2char
            elif ret is None:
                ret = 0

    return ret


def strlen(state: State, s: Union[int, Expression]):
    """
    strlen symbolic model.

    Algorithm: Walks from end of string not including NULL building ITE tree when current byte is symbolic.

    :param State state: current program state
    :param int s: Address of string
    :return: Symbolic strlen result
    :rtype: Expression or int
    """

    cpu = state.cpu

    if issymbolic(s):
        raise ConcretizeArgument(state.cpu, 1)

    zero_idx = _find_zero(cpu, state.constraints, s)

    ret = zero_idx

    for offset in range(zero_idx - 1, -1, -1):
        byt = cpu.read_int(s + offset, 8)
        if issymbolic(byt):
            ret = ITEBV(cpu.address_bit_size, byt == 0, offset, ret)

    return ret


def strcpy(state: State, dst: Union[int, Expression], src: [int, Expression]) -> int:
    """
    strcpy symbolic model

    Algorithm: Copy every byte from the src to dst until finding a byte that will is or must be '\000'

    :param state: current program state
    :param dst: destination string address
    :param src: source string address
    :return: pointer to the dst
    """
    if issymbolic(src):
        raise ConcretizeArgument(state.cpu, 1)

    if issymbolic(dst):
        raise ConcretizeArgument(state.cpu, 2)

    cpu = state.cpu
    constrs = state.constraints
    ret = dst
    c = cpu.read_int(src, 8)
    # Copy until '\000' is reached or symbolic memory that can be '\000'
    while (issymbolic(c) and not Z3Solver.instance().can_be_true(constrs, c == 0)) or c != 0:
        cpu.write_int(dst, c, 8)
        src += 1
        dst += 1
        c = cpu.read_int(src, 8)

    # Even if the byte was symbolic and constrained to '\000' write a concrete '\000'
    if (issymbolic(c) and not Z3Solver.instance().can_be_true(constrs, c != 0)) or c == 0:
        cpu.write_int(dst, 0, 8)
        return ret

    zeros = _find_zeros(cpu, constrs, src)
    null = zeros[-1]
    # If the symmbolic byte was not constrained to '\000' write the appropriate symbolic bytes
    for offset in range(null, -1, -1):
        src_val = cpu.read_int(src + offset, 8)
        dst_val = cpu.read_int(dst + offset, 8)
        if zeros[-1] == offset:
            c = cpu.read_int(src + offset, 8)
            # Make sure last byte of the copy is always a concrete '\000'
            true_val = ITEBV(cpu.address_bit_size, c == 0, 0, src_val)
            zeros.pop()

        # For every byte that could be null before the current byte add an if then else case to the bitvec tree to set the value to the src or dst byte accordingly
        for zero in reverse(zeros):
            c = cpu.read_int(src + zero, 8)
            true_val = ITEBV(cpu.address_bit_size, c != 0, src_val, dst_val)
        cpu.write(dst + offset, true_val, 8)

    return ret
