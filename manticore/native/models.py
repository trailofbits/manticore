"""
Models here are intended to be passed to :meth:`~manticore.native.state.State.invoke_model`, not invoked directly.
"""

from .cpu.abstractcpu import Cpu, ConcretizeArgument
from .state import State
from ..core.smtlib import issymbolic, BitVec, Expression
from ..core.smtlib.solver import Z3Solver
from ..core.smtlib.operators import AND, OR, ITEBV, ZEXTEND, NOT
from ..core.state import Concretize
from typing import Union, Deque
from collections import deque

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


def strcmp(state: State, s1: Union[int, BitVec], s2: Union[int, BitVec]) -> Union[int, BitVec]:
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


def strlen(state: State, s: Union[int, BitVec]) -> Union[int, BitVec] :
    """
    strlen symbolic model.

    Algorithm: Walks from end of string not including NULL building ITE tree when current byte is symbolic.

    :param State state: current program state
    :param s: Address of string
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


def is_definitely_NULL(byte, constrs) -> bool:
    """
    Checks if a given byte read from memory is NULL.
    This supports both concrete & symbolic byte values.

    :param byte: byte read from memory to be examined
    :param constrs: state constraints
    :return: whether a given byte is NULL or constrained to NULL
    """
    if issymbolic(byte):
        return Z3Solver.instance().must_be_true(constrs, byte == 0)
    else:
        return byte == 0


def cant_be_NULL(byte, constrs) -> bool:
    """
    Checks if a given byte read from memory is not NULL or cannot be NULL

    :param byte: byte read from memory to be examined
    :param constrs: state constraints
    :return: whether a given byte is not NULL or cannot be NULL
    """
    if issymbolic(byte):
        return Z3Solver.instance().must_be_true(constrs, byte != 0)
    else:
        return byte != 0


def can_be_NULL(byte, constrs) -> bool:
    """
    Checks if a given byte read from memory can be NULL

    :param byte: byte read from memory to be examined
    :param constrs: state constraints
    :return: whether a given byte is NULL or can be NULL
    """
    if issymbolic(byte):
        return Z3Solver.instance().can_be_true(constrs, byte == 0)
    else:
        return byte == 0


def strcpy(state: State, dst: Union[int, BitVec], src: Union[int, BitVec]) -> Union[int, BitVec]:
    """
    strcpy symbolic model

    Algorithm: Copy every byte from the src to dst until finding a byte that can be or is NULL.
    If the byte is NULL or is constrained to only the NULL value, append the NULL value to dst
    and return. If the value can be NULL or another value write an `Expression` for every following
    byte that sets a value to the src or dst byte according to the preceding bytes until a NULL
    byte or effectively NULL byte is found.

    :param state: current program state
    :param dst: destination string address
    :param src: source string address
    :return: pointer to the dst
    """
    if issymbolic(src):
        raise ConcretizeArgument(state.cpu, 1)

    if issymbolic(dst):
        raise ConcretizeArgument(state.cpu, 0)

    cpu = state.cpu
    constrs = state.constraints
    ret = dst

    # Copy until '\000' is reached or symbolic memory that can be '\000'
    c = cpu.read_int(src, 8)
    while cant_be_NULL(c, constrs):
        cpu.write_int(dst, c, 8)
        src += 1
        dst += 1
        c = cpu.read_int(src, 8)

    # If the byte is symbolic and constrained to '\000', or is concrete and '\000', write concrete val and return
    if is_definitely_NULL(c, constrs):
        cpu.write_int(dst, 0, 8)
        return ret

    offset = 0
    src_val = cpu.read_int(src, 8)
    dst_val = cpu.read_int(dst, 8)
    cond = False  # True # FIXME
    crash = False
    if "strcpy" not in state.context:
        print(f"{offset}: {src_val} -> {dst_val}")
        while not is_definitely_NULL(src_val, constrs):
            print(f"{offset}: {src} -> {dst}")  # Debugging print to be removed later
            if can_be_NULL(src_val, constrs):
                # If a byte can be NULL set the src_val for NULL, build the ITE, & add to the list of nulls
                new_cond = OR(cond, src_val == 0)  # AND(cond, src_val != 0) #FIXME
                src_val = ITEBV(8, src_val != 0, src_val, 0)  # add an ITE just for the NULL
                new_dst = ITEBV(8, cond, dst_val, src_val)  # ITEBV(8, cond, src_val, dst_val) # FIXME
                
                cpu.write_int(dst + offset, new_dst, 8)
                cond = new_cond
            else:
                # If it can't be NULL just build the ITE
                new_dst = ITEBV(8, cond, dst_val, src_val)  # ITEBV(8, cond, src_val, dst_val) # FIXME
                cpu.write_int(dst + offset, new_dst, 8)
            offset += 1

            # Read next byte and crash if src or dst is unreadable/writeable
            if not state.mem.access_ok(src + offset, "r", True) or not state.mem.access_ok(dst + offset, "r", True) or not state.mem.access_ok(dst + offset, "w", True):
                print('Crash')
                crash = True
                #cond = NOT(cond)
                break
            else:
                print(f"{offset}: {src_val} -> {dst_val}")
                src_val = cpu.read_int(src + offset, 8)
                dst_val = cpu.read_int(dst + offset, 8)
        if not crash:
            # Build ITE Tree for NULL byte
            null = ITEBV(8, cond, dst_val, src_val)  # ITEBV(8, cond, 0, dst_val) #FIXME
            cpu.write_int(dst + offset, null, 8)
        state.context["strcpy"] = (crash, cond)

    crash, cond = state.context["strcpy"]
    if crash and issymbolic(cond):
        print('Concreteize')
        for declaration in state.constraints.declarations:
            res = state.constraints.get_variable(declaration.name)
            print('Crash:', crash)
            conc = state.solve_one(res)
            print(f" [{state.id}] \t{declaration.name}:\n [{state.id}] {conc}")
            #symb_smt = state.constraints.to_string()
            #print(f" [{state.id}] \t{declaration.name}:\n [{state.id}] {symb_smt}")
            #state.context["strcpy"] = (False, cond)

        def setstate(state, solution):
            crash, cond = state.context["strcpy"]
            print(cond.constraints.to_string())
            state.context["strcpy"] = (crash, solution)
            print('SET STATE')
            print(state.context["strcpy"])
        raise Concretize("Forking on crash strcpy", expression=cond, setstate=setstate, policy="ONE")
    else:
        print('Write bytes')

    del state.context["strcpy"]
    return ret
