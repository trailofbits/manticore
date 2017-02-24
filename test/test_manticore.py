import unittest

from manticore import Manticore

class ManticoreTest(unittest.TestCase):
    def setUp(self):
        self.m = Manticore('test/binaries/arguments_linux_amd64')

    def test_add_hook(self):
        def tmp(state):
            pass
        entry = 0x00400e40
        self.m.add_hook(entry, tmp)
        self.assertTrue(tmp in self.m._hooks[entry])
