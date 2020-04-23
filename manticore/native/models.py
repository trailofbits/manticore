"""
Models here are intended to be passed to :meth:`~manticore.native.state.State.invoke_model`, not invoked directly.
"""

from .cpu.abstractcpu import ConcretizeArgument, Cpu
from ..core.smtlib import issymbolic
from ..core.smtlib.solver import Z3Solver
from ..core.smtlib.operators import ITEBV, ZEXTEND

from dataclasses import dataclass, field

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


def strcmp(state, s1, s2):
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


def strlen(state, s):
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


@dataclass
class basic_string_class:
    _cpu: Cpu
    addr: int
    _M_dataplus__M_p_addr: int = field(init=False)
    _M_string_length_addr: int = field(init=False)
    _M_local_buf_addr: int = field(init=False)
    _M_allocated_capacity_addr: int = field(init=False)

    def __post_init__(self):
        """
        Represents basic_string object information 
        Naming conventions below preserve basic_string variables for easy reference.
        See: https://github.com/gcc-mirror/gcc/blob/master/libstdc%2B%2B-v3/include/bits/basic_string.h
        """
        # FIXME: automate memory size info and remove the hardcoded memory values below
        # FIXME: symbolic input completely unsupported - make sure concrete input functions correctly first
        self._M_dataplus__M_p_addr = self.addr  # address of c_str address
        self._M_string_length_addr = self.addr + 8  # string length address
        # These two values are contained in a union.
        # See: https://github.com/gcc-mirror/gcc/blob/2930bb321794c241d8df5591a5bf447bf89c6e82/libstdc%2B%2B-v3/include/bits/basic_string.h#L171
        self._M_local_buf_addr = self.addr + 16
        self._M_allocated_capacity_addr = self.addr + 16

        print(f"Length = {self.len}\n{self.addr:016x}")

    def update_len(self, new_len):
        """
        :param new_length: integer of desired new length
        """
        self._cpu.write_int(self._M_string_length_addr, new_len, 64)

    def update_c_str(self, new_str):
        """
        :param new_str: address of the start of new string
        """
        self._cpu.write_int(self._M_dataplus__M_p_addr, new_str, 64)

    @property
    def star_this(self):
        return self._cpu.read_int(self.addr, 256)

    @property
    def c_str(self):
        return self._cpu.read_int(self._M_dataplus__M_p_addr, 64)

    @property
    def len(self):
        return self._cpu.read_int(self._M_string_length_addr, 64)


def basic_string_append_c_str(state, objref, s):
    """
    Extends the basic_string by appending additional characters at the end of its current value

    :param State state: current program state
    :param int objref: Address of basic_string object (this)
    :param int s: Address of char * string to append
    :return: *this
    :rtype: std::basic_string
    """
    cpu = state.cpu
    b_string = basic_string_class(cpu, objref)
    # TODO: add support for when c_str() there is out of space
    # TODO: implement capacity & resize then finish this
    zero_idx = _find_zero(cpu, state.constraints, s)
    for i in range(0, zero_idx):
        src_addr = s + i
        dst_addr = b_string.c_str + b_string.len + i
        c = cpu.read_int(src_addr, 8)
        print(i, ":", c)
        cpu.write_int(dst_addr, c, 8)
    new_len = zero_idx + b_string.len
    print("New length", new_len)
    b_string.update_len(new_len)
    cpu.write_int(b_string.c_str + b_string.len, 0, 8)
    return b_string.star_this


