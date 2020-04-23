"""
Models here are intended to be passed to :meth:`~manticore.native.state.State.invoke_model`, not invoked directly.
"""

from .cpu.abstractcpu import ConcretizeArgument, Cpu
from ..core.smtlib import issymbolic
from ..core.smtlib.solver import Z3Solver
from ..core.smtlib.operators import ITEBV, ZEXTEND
from .models import _find_zero

from dataclasses import dataclass, field

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
        self._S_local_capacity = 15  # 15 chars + '\000'

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

    def resize(self, new_size):
        """
        """
        allocate new mem
        and copy to it
        if not self.is_local:
            delete the old memory 
        return 

    @property
    def star_this(self):
        """
        :return *this: return dereferenced object
        """
        return self._cpu.read_int(self.addr, 256)

    @property
    def c_str(self):
        """
        :return int: internal c_str address
        """
        return self._cpu.read_int(self._M_dataplus__M_p_addr, 64)

    @property
    def len(self):
        """
        :return int: length of string
        """
        return self._cpu.read_int(self._M_string_length_addr, 64)

    @property
    def is_local(self):
        """
        :return bool: whether the string is stored in local buffer
        """
        return self.c_str == self._M_local_buf_addr

    @property
    def capacity(self):
        """
        :return: The size of the storage capacity
        """
        if self.is_local:
            return self._S_local_capacity
        else:
            return self._cpu.read_int(self._M_allocated_capacity_addr, 64)


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


def basic_string_capacity(state, objref):
    """
    The size of the storage capacity currently allocated for the basic_string.

    Member type size_type is an unsigned integral type.
    """
    cpu = state.cpu
    b_string = basic_string_class(cpu, objref)
    return b_string.capacity
