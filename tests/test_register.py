import unittest

from manticore.core.cpu.register import Register

class RegisterTest(unittest.TestCase):
    def test_rd(self):
        r = Register(32)
        self.assertEqual(r.read(), 0)

    def test_basic_write(self):
        r = Register(32)
        r.write(1)
        self.assertEqual(r.read(), 1)

    def test_truncate(self):
        r = Register(32)
        r.write(2**32)
        self.assertEqual(r.read(), 0)

    def test_largest_write(self):
        r = Register(32)
        r.write(0xffffffff)
        self.assertEqual(r.read(), 0xffffffff)

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
