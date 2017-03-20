import unittest
 
from manticore.core.cpu.arm import Armv7RegisterFile as RF
from manticore.core.cpu.arm import *

from capstone.arm import *

class Armv7RF(unittest.TestCase):
    def setUp(self):
        self.r = RF()

    def test_init_state(self):
        self.assertEqual(self.r.read(ARM_REG_R0), 0)

    def test_write_read(self):
        self.r.write(ARM_REG_R0, 1)
        self.assertEqual(self.r.read(ARM_REG_R0), 1)

    def test_write_read_sp(self):
        self.r.write(ARM_REG_SP, 1)
        self.assertEqual(self.r.read(ARM_REG_SP), 1)

    def test_flag_wr(self):
        self.r.write(ARM_REG_APSR_Z, True)
        self.assertEqual(self.r.read(ARM_REG_APSR_Z), True)

    def test_flag_wr_f(self):
        self.r.write(ARM_REG_APSR_Z, False)
        self.assertEqual(self.r.read(ARM_REG_APSR_Z), False)

    def test_reg_name(self):
        self.assertEqual(self.r.reg_name(ARM_REG_R0), 'R0')

    def test_bad_reg_name(self):
        with self.assertRaises(KeyError):
            nonexistant_id = 9999
            self.r.reg_name(nonexistant_id)

    def test_reg_id(self):
        self.assertEqual(self.r.reg_id('R0'), ARM_REG_R0)

    def test_bad_reg_id(self):
        with self.assertRaises(KeyError):
            self.r.reg_id('XXX')

    def test_flag_wr(self):
        self.r.write(ARM_REG_APSR, 0xffffffff)
        self.assertEqual(self.r.read(ARM_REG_APSR), 0xf0000000) #4 more significant bits used
        self.assertEqual(self.r.read(ARM_REG_APSR_V), True)
        self.assertEqual(self.r.read(ARM_REG_APSR_C), True)
        self.assertEqual(self.r.read(ARM_REG_APSR_Z), True)
        self.assertEqual(self.r.read(ARM_REG_APSR_N), True)

        self.r.write(ARM_REG_APSR_N, False)
        self.assertEqual(self.r.read(ARM_REG_APSR), 0x70000000)

        self.r.write(ARM_REG_APSR_Z, False)
        self.assertEqual(self.r.read(ARM_REG_APSR), 0x30000000)

        self.r.write(ARM_REG_APSR_C, False)
        self.assertEqual(self.r.read(ARM_REG_APSR), 0x10000000)

        self.r.write(ARM_REG_APSR_V, False)
        self.assertEqual(self.r.read(ARM_REG_APSR), 0x00000000)


