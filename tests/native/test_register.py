import unittest

from manticore.core.smtlib import Bool, BitVecConstant
from manticore.native.cpu.register import Register


class RegisterTest(unittest.TestCase):
    _multiprocess_can_split_ = True

    def test_rd(self):
        r = Register(32)
        self.assertEqual(r.read(), 0)

    def test_basic_write(self):
        r = Register(32)
        r.write(1)
        self.assertEqual(r.read(), 1)

    def test_truncate(self):
        r = Register(32)
        r.write(2 ** 32)
        self.assertEqual(r.read(), 0)

    def test_largest_write(self):
        r = Register(32)
        r.write(0xFFFFFFFF)
        self.assertEqual(r.read(), 0xFFFFFFFF)

    def test_flag(self):
        r = Register(1)
        self.assertEqual(r.read(), False)

    def test_flag_write(self):
        r = Register(1)
        r.write(True)
        self.assertEqual(r.read(), True)

    def test_flag_trunc(self):
        r = Register(1)
        r.write(3)
        self.assertEqual(r.read(), True)

    def test_bool_write_nonflag(self):
        r = Register(32)
        r.write(True)
        self.assertEqual(r.read(), True)

    def test_Bool(self):
        r = Register(32)
        b = Bool()
        r.write(b)
        self.assertIs(r.read(), b)

    def test_bitvec_flag(self):
        r = Register(1)
        b = BitVecConstant(32, 0)
        r.write(b)
        # __nonzero__ (==) currently unimplemented for Bool
        self.assertTrue(isinstance(r.read(), Bool))

    def test_bitvec(self):
        r = Register(32)
        b = BitVecConstant(32, 0)
        r.write(b)
        self.assertIs(r.read(), b)

    def test_bad_write(self):
        r = Register(32)
        with self.assertRaises(TypeError):
            r.write(dict())
