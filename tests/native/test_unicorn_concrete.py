import unittest
import os

from manticore.native import Manticore
from manticore.core.plugin import Plugin


class ConcretePlugin(Plugin):
    def will_run_callback(self, *_args):
        for state in self.manticore.ready_states:
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
            "XMM0",
            "XMM1",
            "XMM2",
            "XMM3",
            "XMM4",
            "XMM5",
            "XMM6",
            "XMM7",
            "XMM8",
            "XMM9",
            "XMM10",
            "XMM11",
            "XMM12",
            "XMM13",
            "XMM14",
            "XMM15",
            "YMM0",
            "YMM1",
            "YMM2",
            "YMM3",
            "YMM4",
            "YMM5",
            "YMM6",
            "YMM7",
            "YMM8",
            "YMM9",
            "YMM10",
            "YMM11",
            "YMM12",
            "YMM13",
            "YMM14",
            "YMM15",
        }

        concrete_regs = {}
        normal_regs = {}
        for st in self.m.all_states:
            for reg in should_match:
                normal_regs[reg] = getattr(st.platform.current, reg)

        for st in self.concrete_instance.all_states:
            for reg in should_match:
                concrete_regs[reg] = getattr(st.platform.current, reg)

        concrete_regs_vals = {reg: val for reg, val in concrete_regs.items() if reg in should_match}
        normal_regs_vals = {reg: val for reg, val in normal_regs.items() if reg in should_match}
        # To print out a diff
        self.maxDiff = None
        self.assertDictEqual(concrete_regs_vals, normal_regs_vals)

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
