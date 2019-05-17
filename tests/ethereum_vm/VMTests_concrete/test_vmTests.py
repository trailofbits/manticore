"""DO NOT MODIFY: Tests generated from `VMTests/vmTests` with make_VMTests.py"""
import unittest
from binascii import unhexlify

import rlp
import sha3
from rlp.sedes import CountableList, BigEndianInt, Binary

from manticore.core.smtlib import (
    ConstraintSet,
    Z3Solver,
)  # Ignore unused import in non-symbolic tests!
from manticore.core.smtlib.visitors import to_constant
from manticore.platforms import evm
from manticore.utils import config
from manticore.core.state import Concretize


class Log(rlp.Serializable):
    fields = [
        ("address", Binary.fixed_length(20, allow_empty=True)),
        ("topics", CountableList(BigEndianInt(32))),
        ("data", Binary()),
    ]


class EVMTest_vmTests(unittest.TestCase):
    # https://nose.readthedocs.io/en/latest/doc_tests/test_multiprocess/multiprocess.html#controlling-distribution
    _multiprocess_can_split_ = True
    # https://docs.python.org/3.7/library/unittest.html#unittest.TestCase.maxDiff
    maxDiff = None

    SAVED_DEFAULT_FORK = evm.DEFAULT_FORK

    @classmethod
    def setUpClass(cls):
        consts = config.get_group("evm")
        consts.oog = "pedantic"
        evm.DEFAULT_FORK = "frontier"

    @classmethod
    def tearDownClass(cls):
        evm.DEFAULT_FORK = cls.SAVED_DEFAULT_FORK

    def _test_run(self, world):
        result = None
        returndata = b""
        try:
            while True:
                try:
                    world.current_vm.execute()
                except Concretize as e:
                    value = self._solve(world.constraints, e.expression)

                    class fake_state:
                        pass

                    fake_state = fake_state()
                    fake_state.platform = world
                    e.setstate(fake_state, value)
        except evm.EndTx as e:
            result = e.result
            if result in ("RETURN", "REVERT"):
                returndata = self._solve(world.constraints, e.data)
        except evm.StartTx as e:
            self.fail("This tests should not initiate an internal tx (no CALLs allowed)")
        return result, returndata

    def _solve(self, constraints, val):
        results = Z3Solver.instance().get_all_values(constraints, val, maxcnt=3)
        # We constrain all values to single values!
        self.assertEqual(len(results), 1)
        return results[0]

    def test_suicide(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: suicide.json
        sha256sum: 1aa0a61de3c9576faf6ac4f002626210a5315d3132d032162b2934d304a60c1f
        Code:     CALLER
                  SELFDESTRUCT
        """

        def solve(val):
            """
            Those tests are **auto-generated** and `solve` is used in symbolic tests.
            So yes, this returns just val; it makes it easier to generate tests like this.
            """
            return to_constant(val)

        constraints = ConstraintSet()

        blocknumber = 0
        timestamp = 1
        difficulty = 256
        coinbase = 244687034288125203496486448490407391986876152250
        gaslimit = 1000000
        world = evm.EVMWorld(
            constraints,
            blocknumber=blocknumber,
            timestamp=timestamp,
            difficulty=difficulty,
            coinbase=coinbase,
            gaslimit=gaslimit,
        )

        acc_addr = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        acc_code = unhexlify("33ff")
        acc_balance = 100000000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F3947DEF4CF144679DA39C4C32BDC35681
        price = 0x5AF3107A4000
        value = 1000000000000000000
        gas = 100000
        data = ""
        # open a fake tx, no funds send
        world._open_transaction("CALL", address, price, data, caller, value, gas=gas)

        # This variable might seem redundant in some tests - don't forget it is auto generated
        # and there are cases in which we need it ;)
        result, returndata = self._test_run(world)

        # World sanity checks - those should not change, right?
        self.assertEqual(solve(world.block_number()), 0)
        self.assertEqual(solve(world.block_gaslimit()), 1000000)
        self.assertEqual(solve(world.block_timestamp()), 1)
        self.assertEqual(solve(world.block_difficulty()), 256)
        self.assertEqual(solve(world.block_coinbase()), 0x2ADC25665018AA1FE0E6BC666DAC8FC2697FF9BA)

        # Add post checks for account 0xcd1722f3947def4cf144679da39c4c32bdc35681
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xCD1722F3947DEF4CF144679DA39C4C32BDC35681)), 0)
        self.assertEqual(
            solve(world.get_balance(0xCD1722F3947DEF4CF144679DA39C4C32BDC35681)),
            100000000000000000000000,
        )
        self.assertEqual(world.get_code(0xCD1722F3947DEF4CF144679DA39C4C32BDC35681), unhexlify(""))
        # check outs
        self.assertEqual(returndata, unhexlify(""))
        # check logs
        logs = [
            Log(unhexlify("{:040x}".format(l.address)), l.topics, solve(l.memlog))
            for l in world.logs
        ]
        data = rlp.encode(logs)
        self.assertEqual(
            sha3.keccak_256(data).hexdigest(),
            "1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347",
        )

        # test used gas
        self.assertEqual(solve(world.current_vm.gas), 99998)


if __name__ == "__main__":
    unittest.main()
