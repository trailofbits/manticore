import logging

from .utils.helpers import issymbolic
from .core.smtlib.solver import solver
from .core.smtlib.operators import ITEBV, ZEXTEND

logger = logging.getLogger("MODEL")


def _find_zero(cpu, constrs, ptr):
    '''returns offset from ptr to the first byte that is 0 or an Expression that
    cannot
    be
    nonzero
    '''

    offset = 0
    while True:
        byt = cpu.read_int(ptr + offset, 8)

        if issymbolic(byt):
            if not solver.can_be_true(constrs, byt != 0):
                break
        else:
            if byt == 0:
                break

        offset += 1

    return offset


def strcmp(state, a, b):
    '''
    walks from end of string (including minimum offset to a null from both
    strings) to the beginning building tree of ITEs each time either of the
    bytes at current offset is symbolic.

    points of interest:
        - we've been building up a symbolic tree but then encounter two
          concrete bytes that differ. we can throw away the entire symbolic
          tree
        - optimization: if we've been encountering concrete bytes that match
          at the end of the string as we walk forward, and then we encounter
          a pair where one is symbolic, we can forget about that 0 `ret` we've
          been tracking and just replace it with the symbolic subtraction of
          the two

    '''
    cpu = state.cpu
    a_zero_idx = _find_zero(cpu, state.constraints, a)
    b_zero_idx = _find_zero(cpu, state.constraints, b)

    min_zero_idx = min(a_zero_idx, b_zero_idx)

    ret = None

    for offset in range(min_zero_idx + 1)[::-1]:
        achar = cpu.read_int(a + offset, 8)
        achar = ZEXTEND(achar, cpu.address_bit_size)
        bchar = cpu.read_int(b + offset, 8)
        bchar = ZEXTEND(bchar, cpu.address_bit_size)

        if issymbolic(achar) or issymbolic(bchar):
            if ret is None or (not issymbolic(ret) and ret == 0):
                ret = achar - bchar
            else:
                ret = ITEBV(cpu.address_bit_size, achar != bchar, achar - bchar, ret)
        else:
            if achar != bchar:
                ret = achar - bchar
            elif ret is None:
                ret = 0

    return ret
