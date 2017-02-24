import sys, os, struct
import StringIO
import logging
import random
from ..core.smtlib import solver, Expression, Operators
#, Interruption, Syscall, ConcretizeRegister, ConcretizeMemory, ConcretizeArgument, IgnoreAPI
from ..core.cpu.abstractcpu import Interruption, Syscall, \
        ConcretizeRegister, ConcretizeArgument, IgnoreAPI, \
        ConcretizeMemory
from ..core.memory import MemoryException
from ..core.executor import ForkState
from ..utils.helpers import issymbolic

logger = logging.getLogger("MODEL")

def _memset_range(cpu, dst, value, rng):

    minval, maxval, symb_size = rng

    if minval == maxval:
        # no range, just write N elements
        for i in xrange(0, maxval):
            cpu.write_int(dst+i, value, 8)
    else:
        # up to minval doesn't depend on range
        for i in xrange(0, minval):
            cpu.write_int(dst+i, value, 8)

        # write range dependent values
        for i in xrange(minval, maxval):
            cur_v = cpu.read_int(dst+i, 8)
            cpu.write_int(dst+i, Operators.ITEBV(8, symb_size >= i, value, cur_v), 8)

    return dst

def _memmove_range(cpu, dst, src, rng):

    minval, maxval, symb_size = rng

    # read source bytes
    src_bytes = [cpu.read_int(src+i, 8) for i in xrange(0, maxval)]

    if minval == maxval:
        # no range, just write N elements
        for (i,b) in enumerate(src_bytes):
            cpu.write_int(dst+i, b, 8)
    else:
        # up to minval doesn't depend on range
        for i in xrange(0, minval):
            cpu.write_int(dst+i, src_bytes[i], 8)

        # write range dependent values
        for i in xrange(minval, maxval):
            cur_v = cpu.read_int(dst+i, 8)
            cpu.write_int(dst+i, Operators.ITEBV(8, symb_size >= i, src_bytes[i], cur_v), 8)

    return dst

class strings(object):

    @staticmethod
    def memcpy(state, dst, src, size):
        return strings.memmove(state, dst, src, size)

    @staticmethod
    def memmove(state, dst, src, size):
        """void *memmove(void *dest, const void *src, size_t n);"""

        cpu = state.cpu

        if issymbolic(size):
            single_sol = solver.get_all_values(state.constraints, size, maxcnt=2, silent=True)
            if len(single_sol) == 1:
                size = single_sol[0]
                logger.info("memmoving single solution size: {:d}".format(size))
                return _memmove_range(cpu, dst, src, (size, size, None) )
            else:
                conc_min, conc_max = solver.minmax(state.constraints, size)
                logger.info("memmoving sizes: {:d} - {:d}".format(conc_min, conc_max))
                return _memmove_range(cpu, dst, src, (conc_min, conc_max, size) ) 
        else:
            # concrete case
            logger.info("memmoving concrete size: {:d}".format(size))
            return _memmove_range(cpu, dst, src, (size, size, None) )


    @staticmethod
    def memset(state, dst, char, size):
        cpu = state.cpu

        if issymbolic(size):
            single_sol = solver.get_all_values(state.constraints, size, maxcnt=2, silent=True)
            if len(single_sol) == 1:
                size = single_sol[0]
                logger.info("memsetting single solution size: {:d}".format(size))
                return _memset_range(cpu, dst, char, (size, size, None) )
            else:
                conc_min, conc_max = solver.minmax(state.constraints, size)
                logger.info("memsetting in a range: {:d} - {:d}".format(conc_min, conc_max))
                return _memset_range(cpu, dst, char, (conc_min, conc_max, size) ) 
        else:
            # concrete case
            logger.info("memsetting concrete size: {:d}".format(size))
            return _memset_range(cpu, dst, char, (size, size, None) )

    @staticmethod
    def strlen(state, src):
        cpu = state.cpu
        count = 0
        while True:
            value = cpu.read_int(src+count, 8)
            if issymbolic(value):
                if solver.can_be_true(state.constraints, value==0):
                    raise ForkState(value==0)
            elif value == 0:
                break
            count += 1
        return count

    @staticmethod
    def strcpy(state, dst, src):

        cpu = state.cpu
        s = []
        i = 0
        while True:
            value = cpu.read_int(src, 8)
            if not cpu.mem.isWritable(dst+i):
                raise MemoryException("No access writing", dst+i) 
            if issymbolic(value):
                if solver.can_be_true(state.constraints, value==0):
                    raise ConcretizeMemory(src+i)
                else:
                    break
            elif value == 0:
                break
            s.append(value)

        for i in xrange(len(s)):
            cpu.write_int(dst+i, s[i], 8)

class heap(object):

    @staticmethod
    def malloc(cpu, size):
        if issymbolic(size):
            logger.info("malloc(Symbolic Size); concretizing size")
            raise ConcretizeArgument(0)
        else:
            raise IgnoreAPI("malloc({:08x})".format(size))

    @staticmethod
    def realloc(cpu, ptr, size):
        if issymbolic(size):
            logger.info("realloc({}, Symbolic Size); concretizing size".format(str(ptr)))
            raise ConcretizeArgument(1)
        else:
            raise IgnoreAPI("realloc({}, {:08x})".format(str(ptr), size))

    @staticmethod
    def calloc(cpu, count, size):
        if issymbolic(size):
            logger.info("calloc({}, Symbolic Size); concretizing size".format(str(count)))
            raise ConcretizeArgument(1)

        if issymbolic(count):
            logger.info("calloc(Symbolic count, {}); concretizing count".format(str(size)))
            raise ConcretizeArgument(0)

        raise IgnoreAPI("calloc({:08x}, {:08x})".format(count, size))
