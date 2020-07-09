import subprocess
import sys
import time
import unittest

import os
import shutil
import tempfile

DIRPATH = os.path.dirname(__file__)

# TLDR: when we launch `python -m manticore` and one uses PyCharm remote interpreter
# the `python` might not refer to proper interpreter. The `/proc/self/exe` is a workaround
# so one doesn't have to set up virtualenv in a remote interpreter.
PYTHON_BIN = sys.executable


class IntegrationTest(unittest.TestCase):
    _multiprocess_can_split_ = True

    def setUp(self):
        # Create a temporary directory
        self.test_dir = tempfile.mkdtemp()

    def tearDown(self):
        # Remove the directory after the test
        shutil.rmtree(self.test_dir)

    def _simple_cli_run(
        self,
        filename,
        contract=None,
        tx_limit=1,
        in_directory=None,
        args=None,
        workspace=None,
        testcases=False,
    ):
        """
        Simply run the Manticore command line with `filename`
        :param filename: Name of file inside the `contracts` directory
        """
        assert isinstance(args, (list, type(None)))

        working_dir = os.path.join(DIRPATH, "contracts")

        if in_directory:
            working_dir = os.path.join(working_dir, in_directory)

        command = [PYTHON_BIN, "-m", "manticore"]

        if contract:
            command.extend(["--contract", contract])

        if args:
            command.extend(args)

        if workspace:
            command.extend(["--workspace", workspace])

        command.extend(["--txlimit", str(tx_limit)])

        if not testcases:
            command.append("--no-testcases")

        command.append(filename)

        subprocess.check_call(command, stdout=subprocess.PIPE, cwd=working_dir)

    def test_solidity_timeout(self):
        filename = os.path.abspath(os.path.join(DIRPATH, "contracts", "int_overflow.sol"))
        self.assertTrue(filename.startswith(os.getcwd()))
        filename = filename[len(os.getcwd()) + 1 :]
        workspace = os.path.join(self.test_dir, "workspace")

        timeout_secs = 4

        cmd = [
            PYTHON_BIN,
            "-m",
            "manticore",
            "--workspace",
            workspace,
            "--core.timeout",
            str(timeout_secs),
            "--no-color",
            filename,
        ]

        start = time.time()
        output = subprocess.check_output(cmd)
        end = time.time()

        output = list(
            filter(
                lambda l: b"Manticore is only supported on Linux. Proceed at your own risk!"
                not in l,
                output.splitlines(),
            )
        )

        # Because the run will timeout, we don't know the exact line numbers that will appear
        # but this seems as a good default
        self.assertGreaterEqual(len(output), 3)
        # self.assertIn(b'm.c.manticore:INFO: Verbosity set to 1.', output[0])
        self.assertIn(b"m.main:INFO: Registered plugins: ", output[0])
        self.assertIn(b"m.main:INFO: Beginning analysis", output[1])
        self.assertTrue(
            any(b"m.e.manticore:INFO: Starting symbolic create contract" in o for o in output)
        )

        # self.assertIn(b'm.c.manticore:INFO: Results in ', output[-2])
        # self.assertIn(b'm.c.manticore:INFO: Total time: ', output[-1])

        # Since we count the total time of Python process that runs Manticore, it takes a bit more time
        # e.g. for some finalization like generation of testcases
        self.assertLessEqual(end - start, timeout_secs + 20)

    def test_regressions_676(self):
        issue = {"number": 676, "contract": None, "txlimit": 1}
        self._simple_cli_run(
            f'{issue["number"]}.sol',
            contract=issue["contract"],
            tx_limit=issue["txlimit"],
            in_directory=issue.get("in_directory"),
        )

    def test_regressions_678(self):
        issue = {"number": 678, "contract": None, "txlimit": 1}
        self._simple_cli_run(
            f'{issue["number"]}.sol',
            contract=issue["contract"],
            tx_limit=issue["txlimit"],
            in_directory=issue.get("in_directory"),
        )

    def test_regressions_701(self):
        issue = {"number": 701, "contract": None, "txlimit": 1}
        self._simple_cli_run(
            f'{issue["number"]}.sol',
            contract=issue["contract"],
            tx_limit=issue["txlimit"],
            in_directory=issue.get("in_directory"),
        )

    def test_regressions_714(self):
        issue = {"number": 714, "contract": None, "txlimit": 1}
        self._simple_cli_run(
            f'{issue["number"]}.sol',
            contract=issue["contract"],
            tx_limit=issue["txlimit"],
            in_directory=issue.get("in_directory"),
        )

    def test_regressions_735(self):
        issue = {"number": 735, "contract": None, "txlimit": 2}
        self._simple_cli_run(
            f'{issue["number"]}.sol',
            contract=issue["contract"],
            tx_limit=issue["txlimit"],
            in_directory=issue.get("in_directory"),
        )

    def test_regressions_760(self):
        issue = {"number": 760, "contract": None, "txlimit": 1}
        self._simple_cli_run(
            f'{issue["number"]}.sol',
            contract=issue["contract"],
            tx_limit=issue["txlimit"],
            in_directory=issue.get("in_directory"),
        )

    def test_regressions_780(self):
        issue = {"number": 780, "contract": None, "txlimit": 1}
        self._simple_cli_run(
            f'{issue["number"]}.sol',
            contract=issue["contract"],
            tx_limit=issue["txlimit"],
            in_directory=issue.get("in_directory"),
        )

    def test_regressions_795(self):
        issue = {"number": 795, "contract": None, "txlimit": 1}

        self._simple_cli_run(
            f'{issue["number"]}.sol',
            contract=issue["contract"],
            tx_limit=issue["txlimit"],
            in_directory=issue.get("in_directory"),
        )

    def test_regressions_799(self):
        issue = {"number": 799, "contract": "C", "txlimit": 1}
        self._simple_cli_run(
            f'{issue["number"]}.sol',
            contract=issue["contract"],
            tx_limit=issue["txlimit"],
            in_directory=issue.get("in_directory"),
        )

    def test_regressions_807(self):
        issue = {"number": 807, "contract": "C", "txlimit": 1}
        self._simple_cli_run(
            f'{issue["number"]}.sol',
            contract=issue["contract"],
            tx_limit=issue["txlimit"],
            in_directory=issue.get("in_directory"),
        )

    def test_regressions_808(self):
        issue = {"number": 808, "contract": "C", "txlimit": 1}
        self._simple_cli_run(
            f'{issue["number"]}.sol',
            contract=issue["contract"],
            tx_limit=issue["txlimit"],
            in_directory=issue.get("in_directory"),
        )

    def test_regressions_imports(self):
        """
        This tests Manticore on a contract that imports code from another directory.
        """
        issue = {
            "number": "main/main",
            "contract": "C",
            "txlimit": 1,
            "in_directory": "imports_issue",
        }
        self._simple_cli_run(
            f'{issue["number"]}.sol',
            contract=issue["contract"],
            tx_limit=issue["txlimit"],
            in_directory=issue.get("in_directory"),
        )

    def test_1102(self):
        with tempfile.TemporaryDirectory() as workspace:
            self._simple_cli_run("1102.sol", workspace=workspace, testcases=True)

            with open(os.path.join(workspace, "global.findings")) as gf:
                global_findings = gf.read().splitlines()

        self.assertEqual(global_findings[0], "- Unsigned integer overflow at SUB instruction -")
        self.assertRegex(global_findings[1], "  Contract: 0x[0-9a-f]+  EVM Program counter: 0xaf")
        self.assertEqual(global_findings[2], "  Solidity snippet:")
        self.assertEqual(global_findings[3], "    10  count -= input")
        self.assertEqual(global_findings[4], "")

        self.assertEqual(len(global_findings), 5)

    def test_705(self):
        self._simple_cli_run("705.sol")

    def test_addmod(self):
        """
        (declare-fun BV () (_ BitVec 256))
        (declare-fun BV_2 () (_ BitVec 256))
        (declare-fun BV_1 () (_ BitVec 256))
        (declare-fun a_1 () (_ BitVec 256))(assert (= a_1 (bvmul BV BV_1)))
        (declare-fun a_2 () (_ BitVec 512))(assert (= a_2 ((_ zero_extend 256) BV)))
        (declare-fun a_3 () (_ BitVec 512))(assert (= a_3 ((_ zero_extend 256) BV_1)))
        (declare-fun a_4 () (_ BitVec 512))(assert (= a_4 (bvmul a_2 a_3)))
        (declare-fun a_5 () (_ BitVec 512))(assert (= a_5 ((_ zero_extend 256) BV_2)))
        (declare-fun a_6 () (_ BitVec 512))(assert (= a_6 (bvsmod a_4 a_5)))
        (declare-fun a_7 () (_ BitVec 256))(assert (= a_7 ((_ extract 255 0) a_6)))
        (declare-fun a_8 () (_ BitVec 256))(assert (= a_8 (bvsmod a_1 BV_2)))
        (declare-fun a_9 () Bool)(assert (= a_9 (= a_7 a_8)))
        (assert (not a_9))

        (check-sat)
        """
        from manticore.platforms import evm
        from manticore.core.smtlib import ConstraintSet, Z3Solver, Operators

        constraints = ConstraintSet()

        address = 0x41414141414141414141
        data = b""
        caller = 0x42424242424242424242
        value = 0
        bytecode = ""
        vm = evm.EVM(constraints, address, data, caller, value, bytecode, gas=23000)

        self.assertEqual(vm.ADDMOD(12323, 2343, 20), 6)
        self.assertEqual(vm.ADDMOD(12323, 2343, 0), 0)

        A, B, C = (
            0x780000002090309A004201626B1400041D318000000200008A0080089C042DA7,
            0xF000000740403F7007C012807BED003BE2CE800000060000FFFFBFF7E4087033,
            0x338000080FFFFF64AAAACFFCF7DBFA408000000000000270120000001E7C2ACF,
        )
        self.assertEqual(
            vm.ADDMOD(A, B, C),
            23067954172474524581131069693479689311231082562138745684554374357070230297856,
        )
        a, b, c = (
            constraints.new_bitvec(256),
            constraints.new_bitvec(256),
            constraints.new_bitvec(256),
        )
        constraints.add(a == A)
        constraints.add(b == B)
        constraints.add(c == C)
        result = vm.ADDMOD(a, b, c)
        # 0x32ffffd700d073ae080133f517d922bd000000000007f1611e003fffc9239d00
        self.assertEqual(
            Z3Solver.instance().get_all_values(constraints, result),
            [0x32FFFFD700D073AE080133F517D922BD000000000007F1611E003FFFC9239D00],
        )

    def test_mulmod(self):
        """
        (declare-fun BV () (_ BitVec 256))
        (declare-fun BV_2 () (_ BitVec 256))
        (declare-fun BV_1 () (_ BitVec 256))
        (declare-fun a_1 () (_ BitVec 256))(assert (= a_1 (bvmul BV BV_1)))
        (declare-fun a_2 () (_ BitVec 512))(assert (= a_2 ((_ zero_extend 256) BV)))
        (declare-fun a_3 () (_ BitVec 512))(assert (= a_3 ((_ zero_extend 256) BV_1)))
        (declare-fun a_4 () (_ BitVec 512))(assert (= a_4 (bvmul a_2 a_3)))
        (declare-fun a_5 () (_ BitVec 512))(assert (= a_5 ((_ zero_extend 256) BV_2)))
        (declare-fun a_6 () (_ BitVec 512))(assert (= a_6 (bvsmod a_4 a_5)))
        (declare-fun a_7 () (_ BitVec 256))(assert (= a_7 ((_ extract 255 0) a_6)))
        (declare-fun a_8 () (_ BitVec 256))(assert (= a_8 (bvsmod a_1 BV_2)))
        (declare-fun a_9 () Bool)(assert (= a_9 (= a_7 a_8)))
        (assert (not a_9))

        (check-sat)
        """
        from manticore.platforms import evm
        from manticore.core.smtlib import ConstraintSet, Z3Solver, Operators

        constraints = ConstraintSet()

        address = 0x41414141414141414141
        data = b""
        caller = 0x42424242424242424242
        value = 0
        bytecode = ""
        vm = evm.EVM(constraints, address, data, caller, value, bytecode, gas=23000)

        self.assertEqual(vm.MULMOD(12323, 2343, 20), 9)
        self.assertEqual(vm.MULMOD(12323, 2343, 0), 0)

        A, B, C = (
            110427941548649020598956093796432407239217743554726184882600387580788736,
            1048576,
            4194319,
        )
        self.assertEqual(vm.MULMOD(A, B, C), 2423129)
        a, b, c = (
            constraints.new_bitvec(256),
            constraints.new_bitvec(256),
            constraints.new_bitvec(256),
        )
        constraints.add(a == A)
        constraints.add(b == B)
        constraints.add(c == C)
        result = vm.MULMOD(a, b, c)
        # 0x8000000000000000000000000000000000000000000000000000000082000011
        self.assertEqual(Z3Solver.instance().get_all_values(constraints, result), [2423129])


if __name__ == "__main__":
    unittest.main()
