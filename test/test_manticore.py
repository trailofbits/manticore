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

    def test_hook_dec(self):
        entry = 0x00400e40
        @self.m.hook(entry)
        def tmp(state):
            pass
        self.assertTrue(tmp in self.m._hooks[entry])

    def test_hook_dec_err(self):
        with self.assertRaises(TypeError):
            @self.m.hook('0x00400e40')
            def tmp(state):
                pass
