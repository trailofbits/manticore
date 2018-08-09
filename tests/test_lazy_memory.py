from io import BytesIO
from manticore.core.smtlib import Solver, Operators
from manticore.core.smtlib.expression import *
import unittest
import tempfile, os
import gc, pickle
import fcntl
import resource
import sys
from manticore.core.memory import *
from manticore.utils.helpers import issymbolic


class LazyMemoryTest(unittest.TestCase):
    _multiprocess_can_split_ = True

    def test_basic(self):
        cs = ConstraintSet()
        mem = LazySMemory32(cs)
        mem.mmap(0, 4096, 'rwx', name='map')

        m = mem.maps.pop()
        self.assertIsInstance(m, SentinelMap)
        self.assertEqual(m.name, 'map')

    def test_read(self):
        cs = ConstraintSet()
        mem = LazySMemory32(cs)
        mem.mmap(0, 4096, 'rwx', name='map')

        val_mapped = mem.read(0, 4)
        self.assertIsInstance(val_mapped, Array)

        with self.assertRaises(InvalidMemoryAccess):
            mem.read(8096, 4)

    def test_sym_read_mapped(self):
        cs = ConstraintSet()
        mem = LazySMemory32(cs)
        mem.mmap(0, 4096, 'rwx', name='map')

        addr = cs.new_bitvec(32)
        cs.add(addr >= 2048)
        cs.add(addr < 4096)

        val = mem.read(addr, 4)
        self.assertIsInstance(val, Array)


    def test_lazysymbolic_r(self):
        cs = ConstraintSet()
        mem = LazySMemory32(cs)
        sym = cs.new_bitvec(32)
        val = cs.new_bitvec(8)

        cs.add(sym.uge(0xfff))
        cs.add(sym.ule(0x1010))

        #start with no maps
        self.assertEqual(len(mem.mappings()), 0)

        self.assertRaises(MemoryException, mem.__getitem__, 0x1000)
        self.assertIsInstance(mem[sym], InvalidAccessConstant)
        self.assertRaises(MemoryException, mem.__setitem__, 0x1000, '\x42')

        #alloc/map a byte
        first = mem.mmap(0x1000, 0x1000, 'r')

        self.assertEqual(first, 0x1000)
        self.assertEqual(solver.get_value(cs, mem[0x1000]), 0)
        # self.assertRaises(MemoryException, mem.__getitem__, sym)
        # self.assertRaises(MemoryException, mem.__setitem__, 0x1000, '\x41')
        # self.assertRaises(MemoryException, mem.__setitem__, 0x1000, val)
        # self.assertRaises(MemoryException, mem.__setitem__, sym, '\x41')
        # self.assertRaises(MemoryException, mem.__setitem__, sym, val)


if __name__ == '__main__':
    unittest.main()

