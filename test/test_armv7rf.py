import unittest
 
from manticore.core.cpu.arm import Armv7RegisterFile as RF
from manticore.core.cpu.arm import *

from capstone.arm import *

class Armv7RF(unittest.TestCase):
    def setUp(self):
        self.r = RF()

    def test_init_state(self):
        self.assertEqual(self.r.read('R0'), 0)

    def test_write_read(self):
        self.r.write('R0', 1)
        self.assertEqual(self.r.read('R0'), 1)

    def test_write_read_sp(self):
        self.r.write('SP', 1)
        self.assertEqual(self.r.read('SP'), 1)

    def test_flag_wr(self):
        self.r.write('APSR_Z', True)
        self.assertEqual(self.r.read('APSR_Z'), True)

    def test_flag_wr_f(self):
        self.r.write('APSR_Z', False)
        self.assertEqual(self.r.read('APSR_Z'), False)

    def test_bad_flag_write(self):
        with self.assertRaises(AssertionError) as e:
            self.r.write('APSR_Z', 2)


