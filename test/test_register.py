import unittest

from core.cpu.register import Register

class RegisterTest(unittest.TestCase):
    def test_rd(self):
        r = Register(32)
        self.assertEqual(r.read(), 0)

    def test_rd2(self):
        r = Register(32)
        r.write(1)
        self.assertEqual(r.read(), 1)

    def test_rd3(self):
        r = Register(32)
        r.write(2)
        self.assertEqual(r.read(1), 0)

    def test_rd4(self):
        r = Register(32)
        r.write(7, 2)
        self.assertEqual(r.read(), 3)

    def test_rd5(self):
        r = Register(32)
        r.write(2**32)
        self.assertEqual(r.read(), 0)

    def test_rd6(self):
        r = Register(32)
        r.write(0xffffffff)
        self.assertEqual(r.read(), 0xffffffff)

    def test_rd7(self):
        r = Register(32)
        r.write(0xffffffff)
        self.assertEqual(r.read(16), 0xffff)

    def test_reg1(self):
        r = Register(1)
        self.assertEqual(r.read(), False)

    def test_reg1_write(self):
        r = Register(1)
        r.write(True)
        self.assertEqual(r.read(), True)

    def test_reg1_badwrite(self):
        r = Register(1)
        with self.assertRaises(AssertionError):
            r.write(2)
