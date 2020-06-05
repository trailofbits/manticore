import inspect
import unittest
import os
import shutil
from manticore.ethereum.plugins import LoopDepthLimiter, KeepOnlyIfStorageChanges
from manticore.utils import log

from manticore.ethereum import (
    ManticoreEVM,
    DetectInvalid,
    DetectIntegerOverflow,
    DetectReentrancyAdvanced,
)

THIS_DIR = os.path.dirname(os.path.abspath(__file__))

from manticore.utils import config

config.get_group("evm").oog = "ignore"
config.get_group("core").mprocessing = "single"


class EthBenchmark(unittest.TestCase):
    """ https://consensys.net/diligence/evm-analyzer-benchmark-suite/ """

    def setUp(self):
        self.mevm = ManticoreEVM()
        self.mevm.register_plugin(KeepOnlyIfStorageChanges())
        log.set_verbosity(0)
        self.worksp = self.mevm.workspace

    def tearDown(self):
        self.mevm.finalize()
        shutil.rmtree(self.worksp)

    def _test(self, name, should_find, use_ctor_sym_arg=False):
        """
        Tests DetectInvalid over the consensys benchmark suite
        """
        mevm = self.mevm
        mevm.register_detector(DetectInvalid())
        mevm.register_detector(DetectIntegerOverflow())
        mevm.register_detector(DetectReentrancyAdvanced())

        filename = os.path.join(THIS_DIR, "consensys_benchmark", f"{name}.sol")

        if use_ctor_sym_arg:
            ctor_arg = (mevm.make_symbolic_value(),)
        else:
            ctor_arg = ()

        mevm.multi_tx_analysis(filename, contract_name="Benchmark", args=ctor_arg)
        mevm.finalize()

        expected_findings = set(((c, d) for b, c, d in should_find))
        actual_findings = set(((c, d) for a, b, c, d in mevm.global_findings))
        self.assertEqual(expected_findings, actual_findings)

    def test_assert_minimal(self):
        self._test("assert_minimal", {(95, "INVALID instruction", False)})

    def test_assert_constructor(self):
        self._test("assert_constructor", {(23, "INVALID instruction", True)})

    def test_assert_multitx_1(self):
        self._test("assert_multitx_1", set(), True)

    def test_assert_multitx_2(self):
        self._test("assert_multitx_2", {(150, "INVALID instruction", False)}, True)

    def test_integer_overflow_minimal(self):
        self._test(
            "integer_overflow_minimal",
            {(163, "Unsigned integer overflow at SUB instruction", False)},
        )

    def test_integer_overflow_add(self):
        self._test(
            "integer_overflow_add", {(163, "Unsigned integer overflow at ADD instruction", False)}
        )

    def test_integer_overflow_mul(self):
        self._test(
            "integer_overflow_mul", {(163, "Unsigned integer overflow at MUL instruction", False)}
        )

    def test_integer_overflow_path_1(self):
        self._test("integer_overflow_path_1", set())

    def test_integer_overflow_benign_1(self):
        self._test("integer_overflow_benign_1", set())

    def test_integer_overflow_benign_2(self):
        self._test("integer_overflow_benign_2", set())

    def test_integer_overflow_multitx_onefunc_feasible(self):
        self._test(
            "integer_overflow_multitx_onefunc_feasible",
            {(185, "Unsigned integer overflow at SUB instruction", False)},
        )

    def test_integer_overflow_multitx_onefunc_infeasible(self):
        self._test("integer_overflow_multitx_onefunc_infeasible", set())

    def test_integer_overflow_multitx_multifunc_feasible(self):
        self._test(
            "integer_overflow_multitx_multifunc_feasible",
            {(205, "Unsigned integer overflow at SUB instruction", False)},
        )

    def test_integer_overflow_storageinvariant(self):
        self._test("integer_overflow_storageinvariant", set())

    def test_integer_overflow_mapping_sym_1(self):
        self._test(
            "integer_overflow_mapping_sym_1",
            {(135, "Unsigned integer overflow at SUB instruction", False)},
        )

    def test_integer_overflow_mapping_sym_2(self):
        self._test("integer_overflow_mapping_sym_2", set())

    @unittest.skip("Unsupported")
    def test_attribute_store(self):
        self._test("attribute_store", set())

    @unittest.skip("Unsupported")
    def test_integer_overflow_mapping_strkey(self):
        self._test("integer_overflow_mapping_strkey", set())

    def test_integer_overflow_storagepacking(self):
        self._test("integer_overflow_storagepacking", set())

    @unittest.skip("Unsupported")
    def test_integer_overflow_bytes_param(self):
        self._test("integer_overflow_bytes_param", set())

    def test_integer_overflow_staticarray(self):
        self._test("integer_overflow_staticarray", set())

    def test_integer_overflow_mapping_word(self):
        self._test("integer_overflow_mapping_word", set())

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

    def test_reentrancy_nostateeffect(self):
        name = inspect.currentframe().f_code.co_name[5:]
        self._test(name, set())

    def test_reentrancy_dao_fixed(self):
        name = inspect.currentframe().f_code.co_name[5:]
        self._test(name, set())

    def test_reentrancy_dao(self):
        name = inspect.currentframe().f_code.co_name[5:]
        self._test(name, {(247, "Reentrancy multi-million ether bug", False)})

    @unittest.skip("too slow")  # FIXME #TODO
    def test_eth_tx_order_dependence_multitx_1(self):
        name = inspect.currentframe().f_code.co_name[5:]
        self._test(name, set())


if __name__ == "__main__":
    unittest.main()
