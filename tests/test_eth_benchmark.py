import inspect
import shutil
import struct
import tempfile
import unittest
import os

from manticore.core.plugin import Plugin
from manticore.core.smtlib import ConstraintSet, operators
from manticore.core.smtlib.expression import BitVec
from manticore.core.smtlib import solver
from manticore.core.state import State
from manticore.ethereum import ManticoreEVM, DetectInvalid, DetectIntegerOverflow, Detector, NoAliveStates, ABI, EthereumError
from manticore.platforms.evm import EVMWorld, ConcretizeStack, concretized_args, Return, Stop
from manticore.core.smtlib.visitors import pretty_print, translate_to_smtlib, simplify, to_constant

import shutil

THIS_DIR = os.path.dirname(os.path.abspath(__file__))

# FIXME(mark): Remove these two lines when logging works for ManticoreEVM
from manticore.utils.log import init_logging, set_verbosity
init_logging()
set_verbosity(0)

class EthBenchmark(unittest.TestCase):
    """ https://consensys.net/diligence/evm-analyzer-benchmark-suite/ """
    def setUp(self):
        self.mevm = ManticoreEVM()
        self.mevm.verbosity(0)
        self.worksp = self.mevm.workspace

    def tearDown(self):
        self.mevm=None
        shutil.rmtree(self.worksp)

    def _test(self, name, should_find):
        """
        Tests DetectInvalid over the consensys benchmark suit
        """
        mevm = self.mevm

        mevm.register_detector(DetectInvalid())
        mevm.register_detector(DetectIntegerOverflow())

        filename = os.path.join(THIS_DIR, 'binaries', 'benchmark', '{}.sol'.format(name))

        mevm.multi_tx_analysis(filename, tx_limit=3, args=(mevm.make_symbolic_value(),))

        expected_findings = set(( (c, d) for b, c, d in should_find))
        actual_findings = set(( (c, d) for a, b, c, d in mevm.global_findings))
        self.assertEqual(expected_findings, actual_findings)

    def test_assert_minimal(self):
        self._test('assert_minimal', set([(95, 'INVALID intruction', False)]))

    def test_assert_constructor(self):
        self._test('assert_constructor', set([(23L, 'INVALID intruction', True)]))

    def test_assert_multitx_1(self):
        self._test('assert_multitx_1', set())

    def test_assert_multitx_2(self):
        self._test('assert_multitx_2', set([(150, 'INVALID intruction', False)]))

    def test_integer_overflow_minimal(self):
        self._test('integer_overflow_minimal', set([(163L, 'Unsigned integer overflow at SUB instruction', False)]))

    def test_integer_overflow_add(self):
        self._test('integer_overflow_add', set([(163L, 'Unsigned integer overflow at ADD instruction', False)]))

    def test_integer_overflow_mul(self):
        self._test('integer_overflow_mul', set([(163L, 'Unsigned integer overflow at MUL instruction', False)]))

    def test_integer_overflow_path_1(self):
        self._test('integer_overflow_path_1', set())

    def test_integer_overflow_benign_1(self):
        self._test('integer_overflow_benign_1', set())

    def test_integer_overflow_benign_2(self):
        self._test('integer_overflow_benign_2', set())

    def test_integer_overflow_multitx_onefunc_feasible(self):
        self._test('integer_overflow_multitx_onefunc_feasible', set([(185L, 'Unsigned integer overflow at SUB instruction', False)]))

    def test_integer_overflow_multitx_onefunc_infeasible(self):
        self._test('integer_overflow_multitx_onefunc_infeasible', set())

    def test_integer_overflow_multitx_multifunc_feasible(self):
        self._test('integer_overflow_multitx_multifunc_feasible', set([(205L, 'Unsigned integer overflow at SUB instruction', False)]))

    def test_integer_overflow_storageinvariant(self):
        self._test('integer_overflow_storageinvariant', set())

    def test_integer_overflow_mapping_sym_1(self):
        self._test('integer_overflow_mapping_sym_1', set([(135L, 'Unsigned integer overflow at SUB instruction', False)]))

    def test_integer_overflow_mapping_sym_2(self):
        self._test('integer_overflow_mapping_sym_2', set())

    @unittest.skip("Unsupported")
    def test_attribute_store(self):
        self._test('attribute_store', set())

    @unittest.skip("Unsupported")
    def test_integer_overflow_mapping_strkey(self):
        self._test('integer_overflow_mapping_strkey', set())

    def test_integer_overflow_storagepacking(self):
        self._test('integer_overflow_storagepacking', set())

    @unittest.skip("Unsupported")
    def test_integer_overflow_bytes_param(self):
        self._test('integer_overflow_bytes_param', set())

    def test_integer_overflow_staticarray(self):
        self._test('integer_overflow_staticarray', set())

    def test_integer_overflow_mapping_word(self):
        self._test('integer_overflow_mapping_word', set())

    def test_integer_overflow_mapping_struct(self):
        name = inspect.currentframe().f_code.co_name[5:]
        self._test(name, set())

    def test_integer_overflow_mapping_mapping(self):
        name = inspect.currentframe().f_code.co_name[5:]
        self._test(name, set())

    def test_integer_overflow_mapping_staticarray(self):
        name = inspect.currentframe().f_code.co_name[5:]
        self._test(name, set())

    def test_integer_overflow_dynarray(self):
        name = inspect.currentframe().f_code.co_name[5:]
        self._test(name, set())
