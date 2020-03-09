import unittest
import os
import logging
import filecmp

from manticore.native import Manticore
from manticore.utils.log import get_verbosity, set_verbosity

from manticore.core.plugin import Profiler


class ManticoreTest(unittest.TestCase):
    _multiprocess_can_split_ = True

    def setUp(self):

        dirname = os.path.dirname(__file__)
        self.m = Manticore(os.path.join(dirname, "binaries", "arguments_linux_amd64"))

    def test_profiling_data(self):
        p = Profiler()
        set_verbosity(0)
        self.m.register_plugin(p)
        self.m.run()
        self.m.finalize()
        profile_path = os.path.join(self.m.workspace, "profiling.bin")
        self.assertTrue(os.path.exists(profile_path))
        self.assertTrue(os.path.getsize(profile_path) > 0)

        profile_path_2 = os.path.join(self.m.workspace, "profiling_2.bin")
        with open(profile_path_2, "wb") as f:
            p.save_profiling_data(f)

        self.assertTrue(os.path.exists(profile_path_2))
        self.assertTrue(os.path.getsize(profile_path_2) > 0)

        self.assertTrue(filecmp.cmp(profile_path, profile_path_2))

    def test_add_hook(self):
        def tmp(state):
            pass

        entry = 0x00400E40
        self.m.add_hook(entry, tmp)
        self.assertTrue(tmp in self.m._hooks[entry])

    def test_hook_dec(self):
        entry = 0x00400E40

        @self.m.hook(entry)
        def tmp(state):
            pass

        self.assertTrue(tmp in self.m._hooks[entry])

    def test_hook(self):
        self.m.context["x"] = 0

        @self.m.hook(None)
        def tmp(state):
            with self.m.locked_context() as ctx:
                ctx["x"] = 1
            self.m.kill()

        self.m.run()

        self.assertEqual(self.m.context["x"], 1)

    def test_add_hook_after(self):
        def tmp(state):
            pass

        entry = 0x00400E40
        self.m.add_hook(entry, tmp, after=True)
        assert tmp in self.m._after_hooks[entry]

    def test_hook_after_dec(self):
        entry = 0x00400E40

        @self.m.hook(entry, after=True)
        def tmp(state):
            # Make sure we've executed the instruction at entry and we're at
            # the next one (but before it executes).
            assert state.cpu.PC == 0x00400E42
            self.m.kill()

        self.m.run()

        assert tmp in self.m._after_hooks[entry]

    def test_init_hook(self):
        self.m.context["x"] = 0

        @self.m.init
        def tmp(_state):
            self.m.context["x"] = 1
            self.m.kill()

        self.m.run()

        self.assertEqual(self.m.context["x"], 1)

    def test_hook_dec_err(self):
        with self.assertRaises(TypeError):

            @self.m.hook("0x00400e40")
            def tmp(state):
                pass

    def test_symbol_resolution(self):
        dirname = os.path.dirname(__file__)
        self.m = Manticore(os.path.join(dirname, "binaries", "basic_linux_amd64"))
        self.assertTrue(self.m.resolve("sbrk"), 0x449EE0)

    def test_symbol_resolution_fail(self):
        with self.assertRaises(ValueError):
            self.m.resolve("does_not_exist")

    def test_integration_basic_stdin(self):
        import struct

        dirname = os.path.dirname(__file__)
        self.m = Manticore(os.path.join(dirname, "binaries", "basic_linux_amd64"))
        self.m.run()
        self.m.finalize()
        workspace = self.m._output.store.uri
        with open(os.path.join(workspace, "test_00000000.stdin"), "rb") as f:
            a = struct.unpack("<I", f.read())[0]
        with open(os.path.join(workspace, "test_00000001.stdin"), "rb") as f:
            b = struct.unpack("<I", f.read())[0]
        if a > 0x41:
            self.assertTrue(a > 0x41)
            self.assertTrue(b <= 0x41)
        else:
            self.assertTrue(a <= 0x41)
            self.assertTrue(b > 0x41)


class ManticoreLogger(unittest.TestCase):
    """Make sure we set the logging levels correctly"""

    _multiprocess_can_split_ = True

    def test_logging(self):
        set_verbosity(5)
        self.assertEqual(get_verbosity("manticore.native.cpu.abstractcpu"), logging.DEBUG)
        self.assertEqual(get_verbosity("manticore.ethereum.abi"), logging.DEBUG)

        set_verbosity(1)
        self.assertEqual(get_verbosity("manticore.native.cpu.abstractcpu"), logging.WARNING)
        self.assertEqual(get_verbosity("manticore.ethereum.abi"), logging.INFO)

        set_verbosity(0)
