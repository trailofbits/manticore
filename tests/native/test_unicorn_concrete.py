import unittest
import os

from manticore.native import Manticore
from manticore.core.plugin import Plugin


class ConcretePlugin(Plugin):

    def will_start_run_callback(self, state, *_args):
        state.cpu.emulate_until(0)


class RegisterCapturePlugin(Plugin):

    def will_start_run_callback(self, state, *_args):
        self._cpu = state.cpu

    def did_finish_run_callback(self):
        with self.manticore.locked_context() as context:
            for reg in self._cpu.all_registers:
                context[reg] = getattr(self._cpu, reg)


class ManticornTest(unittest.TestCase):
    _multiprocess_can_split_ = True

    def setUp(self):
        dirname = os.path.dirname(__file__)
        self.m = Manticore(os.path.join(dirname, 'binaries', 'arguments_linux_amd64'),
                           argv=['argv', 'mc', 'argface'])
        self.concrete_instance = Manticore(os.path.join(dirname, 'binaries', 'arguments_linux_amd64'),
                                           argv=['argv', 'mc', 'argface'])

        self.concrete_instance.register_plugin(ConcretePlugin())
        self.concrete_instance.register_plugin(RegisterCapturePlugin())
        self.m.register_plugin(RegisterCapturePlugin())

    def test_register_comparison(self):
        self.m.run()
        self.concrete_instance.run()

        for reg in self.concrete_instance.context:
            self.assertEqual(self.concrete_instance.context[reg],
                             self.m.context[reg])

    def test_integration_basic_stdin(self):
        self.m.run()
        self.concrete_instance.run()

        with open(os.path.join(self.m.workspace, 'test_00000000.stdout'), 'r') as f:
            left = f.read().strip()
        with open(os.path.join(self.concrete_instance.workspace, 'test_00000000.stdout'), 'r') as f:
            right = f.read().strip()

        self.assertEqual(left, right)

