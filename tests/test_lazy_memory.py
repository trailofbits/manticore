from io import BytesIO
from manticore.core.smtlib import Solver, Operators
from manticore.core.smtlib.expression import *
from manticore.core.smtlib.visitors import *
import unittest
import tempfile, os
import gc, pickle
import fcntl
import resource
from itertools import *
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

        for val in val_mapped:
            self.assertIsInstance(val, Expression)

        with self.assertRaises(InvalidMemoryAccess):
            mem.read(8096, 4)

    def test_sym_read_mapped(self):
        cs = ConstraintSet()
        mem = LazySMemory32(cs)
        mem.mmap(0, 4096, 'rwx', name='map')

        addr = cs.new_bitvec(32)
        size = 1

        # constrain on a boundary
        cs.add(addr >= 0xffc)
        cs.add(addr <  0x1002)

        # Ensure that all valid derefs are within mapped memory
        with cs as new_cs:
            new_cs.add(mem.valid_ptr(addr, size))
            vals = solver.get_all_values(new_cs, addr)
            self.assertGreater(len(vals), 0)
            for v in vals:
                print(v)
                self.assertTrue(0 <= v < 4096)

        # Ensure that all invalid derefs are outside of mapped memory
        with cs as new_cs:
            new_cs.add(mem.invalid_ptr(addr, size))
            vals = solver.get_all_values(new_cs, addr)
            self.assertGreater(len(vals), 0)
            for v in vals:
                self.assertFalse(0 <= v < 4096)

        val = mem.read(addr, 1)[0]

        self.assertIsInstance(val, Expression)

    def test_lazysymbolic_basic_constrained_read(self):
        cs = ConstraintSet()
        mem = LazySMemory32(cs)
        sym = cs.new_bitvec(32)

        cs.add(sym.uge(0xfff))
        cs.add(sym.ule(0x1010))

        # Make sure reading with no mappings raises an issue
        self.assertRaises(MemoryException, mem.__getitem__, 0x1000)

        first = mem.mmap(0x1000, 0x1000, 'rw')

        self.assertEqual(first, 0x1000)

        mem.write(0x1000, b'\x00')

        self.assertEqual(solver.get_all_values(cs, mem[0x1000]), [0])

    @unittest.skip("Disabled because it takes 4+ minutes; get_all_values() isn't returning all possible addresses")
    def test_lazysymbolic_constrained_deref(self):
        cs = ConstraintSet()
        mem = LazySMemory32(cs)

        mem.page_bit_size = 12
        Size = 0x1000
        PatternSize = 0x100
        Constant = 0x48
        ConstantMask = 0xff

        if False:
            mem.page_bit_size = 10
            Size = 0x800
            PatternSize = 0x80
            Constant = 0x48
            ConstantMask = 0xff

        first = mem.mmap(Size, Size, 'rw')

        # Fill with increasing bytes
        mem.write(first, bytes(islice(cycle(range(PatternSize)), Size)))

        sym = cs.new_bitvec(32)
        cs.add(mem.valid_ptr(sym))

        vals = mem.read(sym, 4)
        # print("sym:")
        # print(translate_to_smtlib(sym))

        cs.add(vals[0] == Constant)
        cs.add(vals[1] == (Constant+1))

        # print("\nvals:")
        # print(translate_to_smtlib(cs))

        possible_addrs = solver.get_all_values(cs, sym)
        print("possible addrs: ", [hex(a) for a in sorted(possible_addrs)])
        for i in possible_addrs:
            self.assertTrue((i & ConstantMask) == Constant)

        # There are 16 spans with 0x48 in [0x1000, 0x2000]
        self.assertEqual(len(possible_addrs), Size // PatternSize)

if __name__ == '__main__':
    unittest.main()

