import unittest
import os

from manticore.native import Manticore
from manticore.core.plugin import Plugin


class ConcretePlugin(Plugin):
    def will_run_callback(self, ready_states):
        for state in ready_states:
            state.cpu.emulate_until(0)


class RegisterCapturePlugin(Plugin):
    def did_run_callback(self):
        with self.manticore.locked_context("regs", dict) as context:
            for st in self.manticore.terminated_states:
                for reg in st.platform.current.canonical_registers:
                    context[reg] = getattr(st.platform.current, reg)


class ManticornTest(unittest.TestCase):
    _multiprocess_can_split_ = True

    def setUp(self):
        dirname = os.path.dirname(__file__)
        self.m = Manticore(
            os.path.join(dirname, "binaries", "arguments_linux_amd64"),
            argv=["argv", "mc", "argface"],
        )
        self.concrete_instance = Manticore(
            os.path.join(dirname, "binaries", "arguments_linux_amd64"),
            argv=["argv", "mc", "argface"],
        )

        self.concrete_instance.register_plugin(ConcretePlugin())
        """
        self.concrete_instance.register_plugin(RegisterCapturePlugin())
        self.m.register_plugin(RegisterCapturePlugin())
        """

    def test_register_comparison(self):
        self.m.run()
        self.concrete_instance.run()

        should_match = {
            "RAX",
            "RDX",
            "RBX",
            "RSP",
            "RBP",
            "RSI",
            "RDI",
            "R8",
            "R9",
            "R10",
            "R12",
            "R13",
            "R14",
            "R15",
            "RIP",
            "CS",
            "DS",
            "ES",
            "SS",
            "FS",
            "GS",
            "AF",
            "CF",
            "DF",
            "IF",
            "OF",
            "SF",
            "FP0",
            "FP1",
            "FP2",
            "FP3",
            "FP4",
            "FP5",
            "FP6",
            "FP7",
            "FPSW",
            "FPCW",
        }

        concrete_regs = {}
        normal_regs = {}
        self.assertEqual(
            len(list(self.m.terminated_states)), len(list(self.concrete_instance.terminated_states))
        )
        self.assertGreater(len(list(self.m.terminated_states)), 0)
        for st in self.m.terminated_states:
            for reg in should_match:
                normal_regs[reg] = getattr(st.platform.current, reg)

        for st in self.concrete_instance.terminated_states:
            for reg in should_match:
                concrete_regs[reg] = getattr(st.platform.current, reg)

        for reg in should_match:
            self.assertEqual(
                concrete_regs[reg],
                normal_regs[reg],
                f"Mismatch in {reg}: {concrete_regs[reg]} != {normal_regs[reg]}",
            )

    def test_integration_basic_stdout(self):
        self.m.run()
        self.concrete_instance.run()

        self.m.finalize()
        self.concrete_instance.finalize()

        with open(os.path.join(self.m.workspace, "test_00000000.stdout"), "r") as f:
            left = f.read().strip()
        with open(os.path.join(self.concrete_instance.workspace, "test_00000000.stdout"), "r") as f:
            right = f.read().strip()

        self.assertEqual(left, right)
