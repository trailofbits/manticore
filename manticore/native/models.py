"""
Models here are intended to be passed to :meth:`~manticore.native.state.State.invoke_model`, not invoked directly.
"""

from .cpu.abstractcpu import Cpu, ConcretizeArgument
from .state import State
from ..core.smtlib import issymbolic, BitVec
from ..core.smtlib.operators import ITEBV, ZEXTEND
from ..core.state import Concretize
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


def must_be_NULL(state, byte) -> bool:
    """
    Checks if a given byte read from memory is NULL.
    This supports both concrete & symbolic byte values.

    :param byte: byte read from memory to be examined
    :param constrs: state constraints
    :return: whether a given byte is NULL or constrained to NULL
    """
    if issymbolic(byte):
        return state.must_be_true(byte == 0)
    else:
        return byte == 0


def cannot_be_NULL(state, byte) -> bool:
    """
    Checks if a given byte read from memory is not NULL or cannot be NULL

    :param byte: byte read from memory to be examined
    :param constrs: state constraints
    :return: whether a given byte is not NULL or cannot be NULL
    """
    if issymbolic(byte):
        return state.must_be_true(byte != 0)
    else:
        return byte != 0


def can_be_NULL(state, byte) -> bool:
    """
    Checks if a given byte read from memory can be NULL

    :param byte: byte read from memory to be examined
    :param constrs: state constraints
    :return: whether a given byte is NULL or can be NULL
    """
    if issymbolic(byte):
        return state.can_be_true(byte == 0)
    else:
        return byte == 0


def _find_zero(cpu, state, ptr: Union[int, BitVec]) -> int:
    """
    Helper for finding the closest NULL or, effectively NULL byte from a starting address.

    :param Cpu cpu:
    :param ConstraintSet constrs: Constraints for current `State`
    :param int ptr: Address to start searching for a zero from
    :return: Offset from `ptr` to first byte that is 0 or an `Expression` that must be zero
    """

    offset = 0
    while True:
        byte = cpu.read_int(ptr + offset, 8)
        if must_be_NULL(state, byte):
            break
        offset += 1

    return offset


def strcmp(state: State, s1: Union[int, BitVec], s2: Union[int, BitVec]):
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

    :param state: Current program state
    :param s1: Address of string 1
    :param s2: Address of string 2
    :return: Symbolic strcmp result
    :rtype: Expression or int
    """

    cpu = state.cpu

    if issymbolic(s1):
        raise ConcretizeArgument(state.cpu, 1)
    if issymbolic(s2):
        raise ConcretizeArgument(state.cpu, 2)

    s1_zero_idx = _find_zero(cpu, state, s1)
    s2_zero_idx = _find_zero(cpu, state, s2)
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


def strlen_exact(state: State, s: Union[int, BitVec]) -> Union[int, BitVec]:
    """
    strlen symbolic model

    Strategy: produce a state for every symbolic string length for better accuracy

    Algorithm: Counts the number of characters in a string forking every time a symbolic byte
    is found that can be NULL but is not constrained to NULL.

    :param state: current program state
    :param s: Address of string
    :return: Symbolic strlen result
    """

    if issymbolic(s):
        raise ConcretizeArgument(state.cpu, 1)

    cpu = state.cpu

    # Initialize offset based on whether state has been forked in strlen
    if "strlen" not in state.context:
        offset = 0
    else:
        offset = state.context["strlen"]

    c = cpu.read_int(s + offset, 8)
    while not must_be_NULL(state, c):
        # If the byte can be NULL concretize and fork states
        if can_be_NULL(state, c):
            state.context["strlen"] = offset
            raise Concretize("Forking on possible NULL strlen", expression=(c == 0), policy="ALL")

        offset += 1
        c = cpu.read_int(s + offset, 8)

    return offset


def strlen_approx(state: State, s: Union[int, BitVec]) -> Union[int, BitVec]:
    """
    strlen symbolic model

    Strategy: build a result tree to limit state explosion results approximate

    Algorithm: Walks from end of string not including NULL building ITE tree when current byte is symbolic.

    :param state: current program state
    :param s: Address of string
    :return: Symbolic strlen result
    """

    if issymbolic(s):
        raise ConcretizeArgument(state.cpu, 1)

    cpu = state.cpu
    zero_idx = _find_zero(cpu, state, s)

    ret = zero_idx

    for offset in range(zero_idx - 1, -1, -1):
        byt = cpu.read_int(s + offset, 8)
        if issymbolic(byt):
            ret = ITEBV(cpu.address_bit_size, byt == 0, offset, ret)

    return ret


def strcpy(state: State, dst: Union[int, BitVec], src: Union[int, BitVec]) -> Union[int, BitVec]:
    """
    strcpy symbolic model

    Algorithm: Copy every byte from src to dst until finding a byte that is NULL or is
    constrained to only the NULL value. Every time a byte is fouund that can be NULL but
    is not definetly NULL concretize and fork states.

    :param state: current program state
    :param dst: destination string address
    :param src: source string address
    :return: pointer to the dst
    """
    if issymbolic(src):
        raise ConcretizeArgument(state.cpu, 2)

    if issymbolic(dst):
        raise ConcretizeArgument(state.cpu, 1)

    cpu = state.cpu
    ret = dst

    # Initialize offset based on whether state has been forked in strcpy
    if "strcpy" not in state.context:
        offset = 0
    else:
        offset = state.context["strcpy"]

    # Copy until a src_byte is symbolic and constrained to '\000', or is concrete and '\000'
    src_val = cpu.read_int(src + offset, 8)
    while not must_be_NULL(state, src_val):
        cpu.write_int(dst + offset, src_val, 8)

        # If a src byte can be NULL concretize and fork states
        if can_be_NULL(state, src_val):
            state.context["strcpy"] = offset
            raise Concretize("Forking on NULL strcpy", expression=(src_val == 0), policy="ALL")
        offset += 1

        src_val = cpu.read_int(src + offset, 8)

    # Write concrete null for end of string in current state
    cpu.write_int(dst + offset, 0, 8)

    if "strcpy" in state.context:
        del state.context["strcpy"]
    return ret


def strncpy(
    state: State, dst: Union[int, BitVec], src: Union[int, BitVec], n: Union[int, BitVec]
) -> Union[int, BitVec]:
    """
    strncpy symbolic model

    Algorithm:  Copy n bytes from src to dst. If the length of the src string is less than n pad the difference
    with NULL bytes. If a symbolic byte is found that can be NULL but is not definitely NULL fork and concretize states.

    :param state: current program state
    :param dst: destination string address
    :param src: source string address
    :param n: number of bytes to copy
    :return: pointer to the dst
    """

    if issymbolic(dst):
        raise ConcretizeArgument(state.cpu, 1)
    if issymbolic(src):
        raise ConcretizeArgument(state.cpu, 2)
    if issymbolic(n):
        raise ConcretizeArgument(state.cpu, 3)

    cpu = state.cpu
    ret = dst

    # Initialize offset based on whether state has been forked in strncpy
    if "strncpy" not in state.context:
        offset = 0
    else:
        offset = state.context["strncpy"]

    # Copy until a src_byte is symbolic and constrained to '\000', or is concrete and '\000'
    src_val = cpu.read_int(src + offset, 8)
    while offset < n and not must_be_NULL(state, src_val):
        cpu.write_int(dst + offset, src_val, 8)

        # If a src byte can be NULL concretize and fork states
        if can_be_NULL(state, src_val):
            state.context["strncpy"] = offset
            raise Concretize("Forking on NULL strncpy", expression=(src_val == 0), policy="ALL")
        offset += 1

        src_val = cpu.read_int(src + offset, 8)

    # Pad the distance between length of src and n with NULL bytes
    while offset < n:
        cpu.write_int(dst + offset, 0, 8)
        offset += 1

    if "strncpy" in state.context:
        del state.context["strncpy"]
    return ret
