import unittest

from manticore import Manticore

class ManticoreTest(unittest.TestCase):
    def setUp(self):
        self.m = Manticore('tests/binaries/arguments_linux_amd64')

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

    def test_hook(self):
        self.m.context['x'] = 0

        @self.m.hook(None)
        def tmp(state):
            self.m.context['x'] = 1
            self.m.terminate()
        self.m.run()

        self.assertEqual(self.m.context['x'], 1)

    def test_hook_dec_err(self):
        with self.assertRaises(TypeError):
            @self.m.hook('0x00400e40')
            def tmp(state):
                pass

    def test_integration_basic_stdin(self):
        import os, struct
        self.m = Manticore('tests/binaries/basic_linux_amd64')
        self.m.run()
        workspace = os.path.join(os.getcwd(), self.m.workspace)
        with open(os.path.join(workspace, 'test_00000001.stdin')) as f:
            a = struct.unpack('<I', f.read())[0]
        with open(os.path.join(workspace, 'test_00000002.stdin')) as f:
            b = struct.unpack('<I', f.read())[0]
        if a > 0x41:
            self.assertTrue(a > 0x41)
            self.assertTrue(b <= 0x41)
        else:
            self.assertTrue(a <= 0x41)
            self.assertTrue(b > 0x41)
