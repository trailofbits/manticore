from io import BytesIO
import unittest
import tempfile
import os
import gc
import pickle
import fcntl
import resource
from itertools import *
import sys

from manticore.native.memory import *
from manticore.core.smtlib import Z3Solver, Operators, issymbolic
from manticore.core.smtlib.expression import *
from manticore.core.smtlib.visitors import *

solver = Z3Solver.instance()


class LazyMemoryTest(unittest.TestCase):
    _multiprocess_can_split_ = True

    def test_basic(self):
        cs = ConstraintSet()
        mem = LazySMemory32(cs)
        mem.mmap(0, 4096, "rwx", name="map")

        m = mem.maps.pop()
        self.assertIsInstance(m, AnonMap)
        self.assertEqual(m.name, "map")

    def test_read(self):
        cs = ConstraintSet()
        mem = LazySMemory32(cs)
        mem.mmap(0, 4096, "rwx", name="map")

        val_mapped = mem.read(0, 4)

        for val in val_mapped:
            self.assertIsInstance(val, bytes)

        with self.assertRaises(InvalidMemoryAccess):
            mem.read(8096, 4)

    def test_sym_read_mapped(self):
        cs = ConstraintSet()
        mem = LazySMemory32(cs)
        mem.mmap(0, 4096, "rwx", name="map")

        addr = cs.new_bitvec(32)

        # constrain on a boundary
        cs.add(addr >= 0xFFC)
        cs.add(addr < 0x1002)

        # Ensure that all valid derefs are within mapped memory
        with cs as new_cs:
            new_cs.add(mem.valid_ptr(addr))
            vals = solver.get_all_values(new_cs, addr)
            self.assertGreater(len(vals), 0)
            for v in vals:
                print(v)
                self.assertTrue(0 <= v < 4096)

        # Ensure that all invalid derefs are outside of mapped memory
        with cs as new_cs:
            new_cs.add(mem.invalid_ptr(addr))
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

        cs.add(sym.uge(0xFFF))
        cs.add(sym.ule(0x1010))

        # Make sure reading with no mappings raises an issue
        self.assertRaises(MemoryException, mem.__getitem__, 0x1000)

        first = mem.mmap(0x1000, 0x1000, "rw")

        self.assertEqual(first, 0x1000)

        mem.write(0x1000, b"\x00")

        self.assertEqual(solver.get_all_values(cs, mem[0x1000]), [b"\x00"])

    def test_arraymap(self):
        m = ArrayMap(0x1000, 0x1000, "rwx", 32)
        head, tail = m.split(0x1800)

        self.assertEqual(head.start, 0x1000)
        self.assertEqual(tail.start, 0x1800)

        self.assertEqual(len(head), 0x800)
        self.assertEqual(len(tail), 0x800)

        self.assertEqual(head.perms, m.perms)
        self.assertEqual(tail.perms, m.perms)

        reduced = m.__reduce__()
        self.assertIs(reduced[0], ArrayMap)

        sel = m[0x1]
        self.assertIsInstance(sel, ArraySelect)

        pre_array = m._array.array
        m[0x1] = 1
        post_array = m._array.array
        self.assertIsNot(pre_array, post_array)

    def test_lazysymbolic_mmapfile(self):
        mem = LazySMemory32(ConstraintSet())

        # start with no maps
        self.assertEqual(len(mem.mappings()), 0)

        rwx_file = tempfile.NamedTemporaryFile("w+b", delete=False)
        rwx_file.file.write(b"a" * 0x1001)
        rwx_file.close()

        addr_a = mem.mmapFile(0, 0x1000, "rwx", rwx_file.name)

        self.assertEqual(len(mem.mappings()), 1)

        self.assertEqual(mem[addr_a], b"a")
        self.assertEqual(mem[addr_a + 0x1000 // 2], b"a")
        self.assertEqual(mem[addr_a + (0x1000 - 1)], b"a")
        self.assertRaises(MemoryException, mem.__getitem__, addr_a + (0x1000))

        rwx_file = tempfile.NamedTemporaryFile("w+b", delete=False)
        rwx_file.file.write(b"b" * 0x1001)
        rwx_file.close()

        addr_b = mem.mmapFile(0, 0x1000, "rw", rwx_file.name)

        self.assertEqual(len(mem.mappings()), 2)

        self.assertEqual(mem[addr_b], b"b")
        self.assertEqual(mem[addr_b + (0x1000 // 2)], b"b")
        self.assertEqual(mem[addr_b + (0x1000 - 1)], b"b")

        rwx_file = tempfile.NamedTemporaryFile("w+b", delete=False)
        rwx_file.file.write(b"c" * 0x1001)
        rwx_file.close()

        addr_c = mem.mmapFile(0, 0x1000, "rx", rwx_file.name)

        self.assertEqual(len(mem.mappings()), 3)

        self.assertEqual(mem[addr_c], b"c")
        self.assertEqual(mem[addr_c + (0x1000 // 2)], b"c")
        self.assertEqual(mem[addr_c + (0x1000 - 1)], b"c")

        rwx_file = tempfile.NamedTemporaryFile("w+b", delete=False)
        rwx_file.file.write(b"d" * 0x1001)
        rwx_file.close()

        addr_d = mem.mmapFile(0, 0x1000, "r", rwx_file.name)

        self.assertEqual(len(mem.mappings()), 4)

        self.assertEqual(mem[addr_d], b"d")
        self.assertEqual(mem[addr_d + (0x1000 // 2)], b"d")
        self.assertEqual(mem[addr_d + (0x1000 - 1)], b"d")

        rwx_file = tempfile.NamedTemporaryFile("w+b", delete=False)
        rwx_file.file.write(b"e" * 0x1001)
        rwx_file.close()

        addr_e = mem.mmapFile(0, 0x1000, "w", rwx_file.name)

        self.assertEqual(len(mem.mappings()), 5)

        self.assertRaises(MemoryException, mem.__getitem__, addr_e)
        self.assertRaises(MemoryException, mem.__getitem__, addr_e + (0x1000 // 2))
        self.assertRaises(MemoryException, mem.__getitem__, addr_e + (0x1000 - 1))

    def test_lazysymbolic_map_containing(self):
        cs = ConstraintSet()
        mem = LazySMemory32(cs)
        valid = cs.new_bitvec(32)
        invalid = cs.new_bitvec(32)

        mem.mmap(0x1000, 0x1000, "rw")
        m = list(mem._maps)[0]

        cs.add(valid > 0x1000)
        cs.add(valid < 0x1002)

        cs.add(invalid < 0x1000)

        ret = mem._deref_can_succeed(m, valid, 1)
        self.assertTrue(ret)

        ret = mem._deref_can_succeed(m, invalid, 1)
        self.assertFalse(ret)

        ret = mem._deref_can_succeed(m, 0x1000, 1)
        self.assertTrue(ret)

        ret = mem._deref_can_succeed(m, 0x800, 1)
        self.assertFalse(ret)

        ret = mem._deref_can_succeed(m, 0xFFF, 2)
        self.assertFalse(ret)

        ret = mem._deref_can_succeed(m, 0x1000, 2)
        self.assertTrue(ret)

        ret = mem._deref_can_succeed(m, 0x1000, 0xFFF)
        self.assertTrue(ret)

        ret = mem._deref_can_succeed(m, 0x1000, 0x1000)
        self.assertFalse(ret)

    @unittest.skip(
        "Disabled because it takes 4+ minutes; get_all_values() isn't returning all possible addresses"
    )
    def test_lazysymbolic_constrained_deref(self):
        cs = ConstraintSet()
        mem = LazySMemory32(cs)

        mem.page_bit_size = 12
        Size = 0x1000
        PatternSize = 0x100
        Constant = 0x48
        ConstantMask = 0xFF

        if False:
            mem.page_bit_size = 10
            Size = 0x800
            PatternSize = 0x80
            Constant = 0x48
            ConstantMask = 0xFF

        first = mem.mmap(Size, Size, "rw")

        # Fill with increasing bytes
        mem.write(first, bytes(islice(cycle(range(PatternSize)), Size)))

        sym = cs.new_bitvec(32)
        # cs.add(mem.valid_ptr(sym))

        vals = mem.read(sym, 4)
        # print("sym:")
        # print(translate_to_smtlib(sym))

        cs.add(vals[0] == Constant)
        cs.add(vals[1] == (Constant + 1))

        # print("\nvals:")
        # print(translate_to_smtlib(cs))

        possible_addrs = solver.get_all_values(cs, sym)
        print("possible addrs: ", [hex(a) for a in sorted(possible_addrs)])
        for i in possible_addrs:
            self.assertTrue((i & ConstantMask) == Constant)

        # There are 16 spans with 0x48 in [0x1000, 0x2000]
        self.assertEqual(len(possible_addrs), Size // PatternSize)


if __name__ == "__main__":
    unittest.main()
