"""DO NOT MODIFY: Tests generated from `VMTests/vmArithmeticTest` with make_VMTests.py"""
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


class EVMTest_vmArithmeticTest(unittest.TestCase):
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

    def test_smod1(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: smod1.json
        sha256sum: 28ae643524b0b1604bf6855fdba96c6a2edee6933e3d4e299296ff1861bce9b6
        Code:     PUSH1 0x3
                  PUSH1 0x0
                  SUB
                  PUSH1 0x5
                  SMOD
                  PUSH1 0x0
                  SSTORE
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
        acc_code = unhexlify("6003600003600507600055")
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F2947DEF4CF144679DA39C4C32BDC35681
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

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 0)
        self.assertEqual(
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 1000000000000000000
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6),
            unhexlify("6003600003600507600055"),
        )
        # check storage
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x00)), 0x02
        )
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
        self.assertEqual(solve(world.current_vm.gas), 79980)

    def test_expPowerOf256Of256_31(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: expPowerOf256Of256_31.json
        sha256sum: 8d4c69f622e12025ff763880fb81489d2816dd996e567a6fbca9af447c939b46
        Code:     PUSH1 0x1f
                  PUSH2 0x100
                  EXP
                  PUSH2 0x100
                  EXP
                  PUSH1 0x0
                  SSTORE
                  PUSH1 0x1f
                  PUSH1 0xff
                  EXP
                  PUSH2 0x100
                  EXP
                  PUSH1 0x1
                  SSTORE
                  PUSH1 0x1f
                  PUSH2 0x101
                  EXP
                  PUSH2 0x100
                  EXP
                  PUSH1 0x2
                  SSTORE
                  PUSH1 0x1f
                  PUSH2 0x100
                  EXP
                  PUSH1 0xff
                  EXP
                  PUSH1 0x3
                  SSTORE
                  PUSH1 0x1f
                  PUSH1 0xff
                  EXP
                  PUSH1 0xff
                  EXP
                  PUSH1 0x4
                  SSTORE
                  PUSH1 0x1f
                  PUSH2 0x101
                  EXP
                  PUSH1 0xff
                  EXP
                  PUSH1 0x5
                  SSTORE
                  PUSH1 0x1f
                  PUSH2 0x100
                  EXP
                  PUSH2 0x101
                  EXP
                  PUSH1 0x6
                  SSTORE
                  PUSH1 0x1f
                  PUSH1 0xff
                  EXP
                  PUSH2 0x101
                  EXP
                  PUSH1 0x7
                  SSTORE
                  PUSH1 0x1f
                  PUSH2 0x101
                  EXP
                  PUSH2 0x101
                  EXP
                  PUSH1 0x8
                  SSTORE
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
        gaslimit = 10000000
        world = evm.EVMWorld(
            constraints,
            blocknumber=blocknumber,
            timestamp=timestamp,
            difficulty=difficulty,
            coinbase=coinbase,
            gaslimit=gaslimit,
        )

        acc_addr = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        acc_code = unhexlify(
            "601f6101000a6101000a600055601f60ff0a6101000a600155601f6101010a6101000a600255601f6101000a60ff0a600355601f60ff0a60ff0a600455601f6101010a60ff0a600555601f6101000a6101010a600655601f60ff0a6101010a600755601f6101010a6101010a600855"
        )
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F2947DEF4CF144679DA39C4C32BDC35681
        price = 0x5AF3107A4000
        value = 1000000000000000000
        gas = 1000000
        data = ""
        # open a fake tx, no funds send
        world._open_transaction("CALL", address, price, data, caller, value, gas=gas)

        # This variable might seem redundant in some tests - don't forget it is auto generated
        # and there are cases in which we need it ;)
        result, returndata = self._test_run(world)

        # World sanity checks - those should not change, right?
        self.assertEqual(solve(world.block_number()), 0)
        self.assertEqual(solve(world.block_gaslimit()), 10000000)
        self.assertEqual(solve(world.block_timestamp()), 1)
        self.assertEqual(solve(world.block_difficulty()), 256)
        self.assertEqual(solve(world.block_coinbase()), 0x2ADC25665018AA1FE0E6BC666DAC8FC2697FF9BA)

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 0)
        self.assertEqual(
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 1000000000000000000
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6),
            unhexlify(
                "601f6101000a6101000a600055601f60ff0a6101000a600155601f6101010a6101000a600255601f6101000a60ff0a600355601f60ff0a60ff0a600455601f6101010a60ff0a600555601f6101000a6101010a600655601f60ff0a6101010a600755601f6101010a6101010a600855"
            ),
        )
        # check storage
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x03)), 0x01
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x04)),
            0xF9CB87F5B1AB58602F52A1E9D392E5675B86A59A53943A8D4EC2A915DC9DFEFF,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x05)),
            0x893D729A64E318860EC5047E70E598DA163EB41E71E74B04DFD4712D419F00FF,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x06)), 0x01
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x07)),
            0xEE5F2839C1B4F6CA05E6FDB04E2FB49C0F860B3765C27DC781A150CB7F9FFF01,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x08)),
            0xB4C358E3C6BCDDFB509EA487D733DF0E1854F29C3B6BFD4A8CAABE3F609F0101,
        )
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
        self.assertEqual(solve(world.current_vm.gas), 861772)

    def test_expPowerOf256Of256_12(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: expPowerOf256Of256_12.json
        sha256sum: 7ddde6fa841550682fd17bfdd5fae3238025df9241a1f9bfaaece1fcf83ef750
        Code:     PUSH1 0xc
                  PUSH2 0x100
                  EXP
                  PUSH2 0x100
                  EXP
                  PUSH1 0x0
                  SSTORE
                  PUSH1 0xc
                  PUSH1 0xff
                  EXP
                  PUSH2 0x100
                  EXP
                  PUSH1 0x1
                  SSTORE
                  PUSH1 0xc
                  PUSH2 0x101
                  EXP
                  PUSH2 0x100
                  EXP
                  PUSH1 0x2
                  SSTORE
                  PUSH1 0xc
                  PUSH2 0x100
                  EXP
                  PUSH1 0xff
                  EXP
                  PUSH1 0x3
                  SSTORE
                  PUSH1 0xc
                  PUSH1 0xff
                  EXP
                  PUSH1 0xff
                  EXP
                  PUSH1 0x4
                  SSTORE
                  PUSH1 0xc
                  PUSH2 0x101
                  EXP
                  PUSH1 0xff
                  EXP
                  PUSH1 0x5
                  SSTORE
                  PUSH1 0xc
                  PUSH2 0x100
                  EXP
                  PUSH2 0x101
                  EXP
                  PUSH1 0x6
                  SSTORE
                  PUSH1 0xc
                  PUSH1 0xff
                  EXP
                  PUSH2 0x101
                  EXP
                  PUSH1 0x7
                  SSTORE
                  PUSH1 0xc
                  PUSH2 0x101
                  EXP
                  PUSH2 0x101
                  EXP
                  PUSH1 0x8
                  SSTORE
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
        gaslimit = 10000000
        world = evm.EVMWorld(
            constraints,
            blocknumber=blocknumber,
            timestamp=timestamp,
            difficulty=difficulty,
            coinbase=coinbase,
            gaslimit=gaslimit,
        )

        acc_addr = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        acc_code = unhexlify(
            "600c6101000a6101000a600055600c60ff0a6101000a600155600c6101010a6101000a600255600c6101000a60ff0a600355600c60ff0a60ff0a600455600c6101010a60ff0a600555600c6101000a6101010a600655600c60ff0a6101010a600755600c6101010a6101010a600855"
        )
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F2947DEF4CF144679DA39C4C32BDC35681
        price = 0x5AF3107A4000
        value = 1000000000000000000
        gas = 1000000
        data = ""
        # open a fake tx, no funds send
        world._open_transaction("CALL", address, price, data, caller, value, gas=gas)

        # This variable might seem redundant in some tests - don't forget it is auto generated
        # and there are cases in which we need it ;)
        result, returndata = self._test_run(world)

        # World sanity checks - those should not change, right?
        self.assertEqual(solve(world.block_number()), 0)
        self.assertEqual(solve(world.block_gaslimit()), 10000000)
        self.assertEqual(solve(world.block_timestamp()), 1)
        self.assertEqual(solve(world.block_difficulty()), 256)
        self.assertEqual(solve(world.block_coinbase()), 0x2ADC25665018AA1FE0E6BC666DAC8FC2697FF9BA)

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 0)
        self.assertEqual(
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 1000000000000000000
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6),
            unhexlify(
                "600c6101000a6101000a600055600c60ff0a6101000a600155600c6101010a6101000a600255600c6101000a60ff0a600355600c60ff0a60ff0a600455600c6101010a60ff0a600555600c6101000a6101010a600655600c60ff0a6101010a600755600c6101010a6101010a600855"
            ),
        )
        # check storage
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x03)),
            0xB0E95B83A36CE98218879EC55C33085514FF7F00000000000000000000000001,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x04)),
            0xC482AB56EC19186DC48C88F30861A850B2253B1EA6DC021589E569BD47F400FF,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x05)),
            0xCF45C7F9AF4BBE4A83055B55B97777AD5E0A3F08B129C9AE208C5D713C0C00FF,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x06)),
            0xA5CBB62A421049B0F000B68FB921F7AA6AFF8100000000000000000000000001,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x07)),
            0x3BDE6CA66DFFE1BF5D727C3EDEA74C7A4AF43B3912E6256D37705C8F3BF40101,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x08)),
            0x3F49A1E40C5213AA4FFED57EB4C1AD2D181B2AAA289E9D59C2256C43480C0101,
        )
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
        self.assertEqual(solve(world.current_vm.gas), 863482)

    def test_add3(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: add3.json
        sha256sum: 094abae4a6da6e1506b01dd667c165c5c9c068fac674548685885f3c8fcc58cc
        Code:     PUSH1 0x0
                  PUSH1 0x0
                  ADD
                  PUSH1 0x0
                  SSTORE
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
        acc_code = unhexlify("6000600001600055")
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F2947DEF4CF144679DA39C4C32BDC35681
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

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 0)
        self.assertEqual(
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 1000000000000000000
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6), unhexlify("6000600001600055")
        )
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
        self.assertEqual(solve(world.current_vm.gas), 94988)

    def test_mulmod4(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: mulmod4.json
        sha256sum: 31c06c40acc8ab37bb205e24939f1bd09a7e65eac4e3976f5ca436b07af2f3cc
        Code:     PUSH1 0x64
                  PUSH1 0x1b
                  PUSH1 0x25
                  MULMOD
                  PUSH1 0x0
                  MSTORE8
                  PUSH1 0x0
                  PUSH1 0x1
                  RETURN
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
        acc_code = unhexlify("6064601b60250960005360006001f3")
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F2947DEF4CF144679DA39C4C32BDC35681
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

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 0)
        self.assertEqual(
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 1000000000000000000
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6),
            unhexlify("6064601b60250960005360006001f3"),
        )
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
        self.assertEqual(solve(world.current_vm.gas), 99968)

    def test_divBoostBug(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: divBoostBug.json
        sha256sum: fe3275283df2833162d7118278032b6c1671b682b097bb88d3cb70eb054498ba
        Code:     PUSH32 0x1dae6076b981dae6076b981dae6076b981dae6076b981dae6076b981dae6077
                  PUSH32 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffba
                  DIV
                  PUSH1 0x0
                  SSTORE
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
        acc_code = unhexlify(
            "7f01dae6076b981dae6076b981dae6076b981dae6076b981dae6076b981dae60777fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffba04600055"
        )
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F2947DEF4CF144679DA39C4C32BDC35681
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

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 0)
        self.assertEqual(
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 1000000000000000000
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6),
            unhexlify(
                "7f01dae6076b981dae6076b981dae6076b981dae6076b981dae6076b981dae60777fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffba04600055"
            ),
        )
        # check storage
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x00)), 0x89
        )
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
        self.assertEqual(solve(world.current_vm.gas), 79986)

    def test_mod4(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: mod4.json
        sha256sum: e331db234769811883d87ea184e6e1ac118b59906328047791f12e2461435a20
        Code:     PUSH1 0x3
                  PUSH1 0x2
                  PUSH1 0x0
                  SUB
                  MOD
                  PUSH1 0x0
                  SSTORE
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
        acc_code = unhexlify("6003600260000306600055")
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F2947DEF4CF144679DA39C4C32BDC35681
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

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 0)
        self.assertEqual(
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 1000000000000000000
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6),
            unhexlify("6003600260000306600055"),
        )
        # check storage
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x00)), 0x02
        )
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
        self.assertEqual(solve(world.current_vm.gas), 79980)

    def test_sdiv1(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: sdiv1.json
        sha256sum: d224466fd0d90938d79dddd9910147a2f173ca4444eeda966e38419edfc56fad
        Code:     PUSH32 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
                  PUSH1 0x0
                  SUB
                  PUSH32 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
                  SDIV
                  PUSH1 0x0
                  SSTORE
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
        acc_code = unhexlify(
            "7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff6000037fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff05600055"
        )
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F2947DEF4CF144679DA39C4C32BDC35681
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

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 0)
        self.assertEqual(
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 1000000000000000000
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6),
            unhexlify(
                "7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff6000037fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff05600055"
            ),
        )
        # check storage
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x00)),
            0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF,
        )
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
        self.assertEqual(solve(world.current_vm.gas), 79980)

    def test_modByZero(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: modByZero.json
        sha256sum: 975e8402d3cdcd650cbe38ddde963ee0f001c44eb91be662ab5ad30d092bf3ec
        Code:     PUSH1 0x1
                  PUSH1 0x0
                  PUSH1 0x3
                  MOD
                  SUB
                  PUSH1 0x0
                  SSTORE
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
        acc_code = unhexlify("6001600060030603600055")
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F2947DEF4CF144679DA39C4C32BDC35681
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

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 0)
        self.assertEqual(
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 1000000000000000000
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6),
            unhexlify("6001600060030603600055"),
        )
        # check storage
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x00)),
            0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF,
        )
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
        self.assertEqual(solve(world.current_vm.gas), 79980)

    def test_expPowerOf256_31(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: expPowerOf256_31.json
        sha256sum: 03ddf07eca732084776985584806b3a2b90af3536705f92c286daa0f723f46c3
        Code:     PUSH1 0x1f
                  PUSH2 0x100
                  EXP
                  PUSH1 0x0
                  SSTORE
                  PUSH1 0x1f
                  PUSH1 0xff
                  EXP
                  PUSH1 0x1
                  SSTORE
                  PUSH1 0x1f
                  PUSH2 0x101
                  EXP
                  PUSH1 0x2
                  SSTORE
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
        acc_code = unhexlify("601f6101000a600055601f60ff0a600155601f6101010a600255")
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F2947DEF4CF144679DA39C4C32BDC35681
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

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 0)
        self.assertEqual(
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 1000000000000000000
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6),
            unhexlify("601f6101000a600055601f60ff0a600155601f6101010a600255"),
        )
        # check storage
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x00)),
            0x0100000000000000000000000000000000000000000000000000000000000000,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x01)),
            0xE2BFE95C5D7067567402DD9D7235FC088AC84EAB8113BF8D7E3C288D2F1EFF,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x02)),
            0x0120E30C8C1BB25C9D2219EA196C17DED3D775B231BBD28005B131FA90D11F01,
        )
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
        self.assertEqual(solve(world.current_vm.gas), 39913)

    def test_stop(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: stop.json
        sha256sum: 69c1ebfcd7bc87b206fa27fffa8a54a486a453cf86bfff26a0ae7270dffabb3c
        Code:     STOP
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
        acc_code = unhexlify("00")
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F2947DEF4CF144679DA39C4C32BDC35681
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

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 0)
        self.assertEqual(
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 1000000000000000000
        )
        self.assertEqual(world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6), unhexlify("00"))
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
        self.assertEqual(solve(world.current_vm.gas), 100000)

    def test_mulmoddivByZero3(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: mulmoddivByZero3.json
        sha256sum: eca0b9c5545b22116e69cf05c171e68e0f1a6ceefd1e6b24b8b06e08a40bea31
        Code:     PUSH1 0x0
                  PUSH1 0x0
                  PUSH1 0x0
                  MULMOD
                  PUSH1 0x1
                  SUB
                  PUSH1 0x0
                  SSTORE
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
        acc_code = unhexlify("60006000600009600103600055")
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F2947DEF4CF144679DA39C4C32BDC35681
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

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 0)
        self.assertEqual(
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 1000000000000000000
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6),
            unhexlify("60006000600009600103600055"),
        )
        # check storage
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x00)), 0x01
        )
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
        self.assertEqual(solve(world.current_vm.gas), 79974)

    def test_expPowerOf256_5(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: expPowerOf256_5.json
        sha256sum: 5b2e8fdcb47b11d7de771c1ac0aa386f0ba6c1a51d423d968587caeffbec6459
        Code:     PUSH1 0x5
                  PUSH2 0x100
                  EXP
                  PUSH1 0x0
                  SSTORE
                  PUSH1 0x5
                  PUSH1 0xff
                  EXP
                  PUSH1 0x1
                  SSTORE
                  PUSH1 0x5
                  PUSH2 0x101
                  EXP
                  PUSH1 0x2
                  SSTORE
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
        acc_code = unhexlify("60056101000a600055600560ff0a60015560056101010a600255")
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F2947DEF4CF144679DA39C4C32BDC35681
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

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 0)
        self.assertEqual(
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 1000000000000000000
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6),
            unhexlify("60056101000a600055600560ff0a60015560056101010a600255"),
        )
        # check storage
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x00)),
            0x010000000000,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x01)),
            0xFB09F604FF,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x02)),
            0x01050A0A0501,
        )
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
        self.assertEqual(solve(world.current_vm.gas), 39913)

    def test_sdiv_dejavu(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: sdiv_dejavu.json
        sha256sum: 452081e3e414078883f6a88fe922841ab480e6786afd74e40ff8cb960db4cb9d
        Code:     PUSH1 0x5
                  PUSH1 0x9
                  PUSH1 0x0
                  SUB
                  SDIV
                  DUP1
                  PUSH1 0x0
                  SSTORE
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
        acc_code = unhexlify("600560096000030580600055")
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F2947DEF4CF144679DA39C4C32BDC35681
        price = 0x1
        value = 1000000000000000000
        gas = 10000000
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

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 0)
        self.assertEqual(
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 1000000000000000000
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6),
            unhexlify("600560096000030580600055"),
        )
        # check storage
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x00)),
            0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF,
        )
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
        self.assertEqual(solve(world.current_vm.gas), 9979977)

    def test_mulmod2_0(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: mulmod2_0.json
        sha256sum: cc684081a03672440715b213e55d41c6b40b5f906d5729227eca121ffb459d9f
        Code:     PUSH1 0x3
                  PUSH1 0x1
                  PUSH1 0x5
                  PUSH1 0x0
                  SUB
                  MULMOD
                  PUSH1 0x3
                  PUSH1 0x5
                  PUSH1 0x0
                  SUB
                  SMOD
                  EQ
                  PUSH1 0x0
                  SSTORE
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
        acc_code = unhexlify("60036001600560000309600360056000030714600055")
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F2947DEF4CF144679DA39C4C32BDC35681
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

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 0)
        self.assertEqual(
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 1000000000000000000
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6),
            unhexlify("60036001600560000309600360056000030714600055"),
        )
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
        self.assertEqual(solve(world.current_vm.gas), 94954)

    def test_smod_i256min1(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: smod_i256min1.json
        sha256sum: 4fab8396013a69a2e27b500d1eafc17724e7d1746a336264f1ebfd3c16ea41e9
        Code:     PUSH1 0x1
                  PUSH1 0x0
                  SUB
                  PUSH32 0x8000000000000000000000000000000000000000000000000000000000000000
                  PUSH1 0x0
                  SUB
                  SMOD
                  PUSH1 0x0
                  SSTORE
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
        acc_code = unhexlify(
            "60016000037f800000000000000000000000000000000000000000000000000000000000000060000307600055"
        )
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F2947DEF4CF144679DA39C4C32BDC35681
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

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 0)
        self.assertEqual(
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 1000000000000000000
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6),
            unhexlify(
                "60016000037f800000000000000000000000000000000000000000000000000000000000000060000307600055"
            ),
        )
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
        self.assertEqual(solve(world.current_vm.gas), 94974)

    def test_mulmoddivByZero2(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: mulmoddivByZero2.json
        sha256sum: b5ecff08a9253fd2c07fe2355faafe42448e83131c0844f820dc30bc9aa5f3a3
        Code:     PUSH1 0x0
                  PUSH1 0x0
                  PUSH1 0x1
                  MULMOD
                  PUSH1 0x0
                  SSTORE
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
        acc_code = unhexlify("60006000600109600055")
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F2947DEF4CF144679DA39C4C32BDC35681
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

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 0)
        self.assertEqual(
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 1000000000000000000
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6),
            unhexlify("60006000600109600055"),
        )
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
        self.assertEqual(solve(world.current_vm.gas), 94980)

    def test_expPowerOf256_2(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: expPowerOf256_2.json
        sha256sum: b012e7ef19b7246c611040efe1cd4c02a0011c48749337388f0c59d2a3679a08
        Code:     PUSH1 0x2
                  PUSH2 0x100
                  EXP
                  PUSH1 0x0
                  SSTORE
                  PUSH1 0x2
                  PUSH1 0xff
                  EXP
                  PUSH1 0x1
                  SSTORE
                  PUSH1 0x2
                  PUSH2 0x101
                  EXP
                  PUSH1 0x2
                  SSTORE
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
        acc_code = unhexlify("60026101000a600055600260ff0a60015560026101010a600255")
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F2947DEF4CF144679DA39C4C32BDC35681
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

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 0)
        self.assertEqual(
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 1000000000000000000
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6),
            unhexlify("60026101000a600055600260ff0a60015560026101010a600255"),
        )
        # check storage
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x00)), 0x010000
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x01)), 0xFE01
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x02)), 0x010201
        )
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
        self.assertEqual(solve(world.current_vm.gas), 39913)

    def test_exp7(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: exp7.json
        sha256sum: fc5158a5d8f866285b0dc0feab44a7f04cd9d5c70392ac3a121ee7f5f449b92b
        Code:     PUSH2 0x101
                  PUSH1 0x2
                  EXP
                  PUSH1 0x0
                  SSTORE
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
        acc_code = unhexlify("61010160020a600055")
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F2947DEF4CF144679DA39C4C32BDC35681
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

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 0)
        self.assertEqual(
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 1000000000000000000
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6),
            unhexlify("61010160020a600055"),
        )
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
        self.assertEqual(solve(world.current_vm.gas), 94961)

    def test_expPowerOf2_8(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: expPowerOf2_8.json
        sha256sum: dc827c7432f16db5c78b63f434ca2dc24762a4bf7827cc3f487fffe08a0d452c
        Code:     PUSH1 0x8
                  PUSH1 0x2
                  EXP
                  PUSH1 0x0
                  SSTORE
                  PUSH1 0x7
                  PUSH1 0x2
                  EXP
                  PUSH1 0x1
                  SSTORE
                  PUSH1 0x9
                  PUSH1 0x2
                  EXP
                  PUSH1 0x2
                  SSTORE
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
        acc_code = unhexlify("600860020a600055600760020a600155600960020a600255")
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F2947DEF4CF144679DA39C4C32BDC35681
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

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 0)
        self.assertEqual(
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 1000000000000000000
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6),
            unhexlify("600860020a600055600760020a600155600960020a600255"),
        )
        # check storage
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x00)), 0x0100
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x01)), 0x80
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x02)), 0x0200
        )
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
        self.assertEqual(solve(world.current_vm.gas), 39913)

    def test_mod3(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: mod3.json
        sha256sum: 3ff47f92fc773259070c4ecd80ecc707390c4bf33c53bf8ede1405e598e4e563
        Code:     PUSH1 0x0
                  PUSH1 0x3
                  MOD
                  PUSH1 0x0
                  SSTORE
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
        acc_code = unhexlify("6000600306600055")
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F2947DEF4CF144679DA39C4C32BDC35681
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

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 0)
        self.assertEqual(
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 1000000000000000000
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6), unhexlify("6000600306600055")
        )
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
        self.assertEqual(solve(world.current_vm.gas), 94986)

    def test_exp2(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: exp2.json
        sha256sum: 7f8a88cc52c669687508ef474246c30a969cdecf4eb6a508600be3dc404317dd
        Code:     PUSH4 0x7fffffff
                  PUSH4 0x7fffffff
                  EXP
                  PUSH1 0x0
                  SSTORE
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
        acc_code = unhexlify("637fffffff637fffffff0a600055")
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F2947DEF4CF144679DA39C4C32BDC35681
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

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 0)
        self.assertEqual(
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 1000000000000000000
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6),
            unhexlify("637fffffff637fffffff0a600055"),
        )
        # check storage
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x00)),
            0xBC8CCCCCCCC888888880000000AAAAAAB00000000FFFFFFFFFFFFFFF7FFFFFFF,
        )
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
        self.assertEqual(solve(world.current_vm.gas), 79941)

    def test_expPowerOf256Of256_32(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: expPowerOf256Of256_32.json
        sha256sum: 3aeec0dc1d899e00954d8cc12a7eb4e4ea8a79d53b763de0ed38bbd7f70dc8e0
        Code:     PUSH1 0x20
                  PUSH2 0x100
                  EXP
                  PUSH2 0x100
                  EXP
                  PUSH1 0x0
                  SSTORE
                  PUSH1 0x20
                  PUSH1 0xff
                  EXP
                  PUSH2 0x100
                  EXP
                  PUSH1 0x1
                  SSTORE
                  PUSH1 0x20
                  PUSH2 0x101
                  EXP
                  PUSH2 0x100
                  EXP
                  PUSH1 0x2
                  SSTORE
                  PUSH1 0x20
                  PUSH2 0x100
                  EXP
                  PUSH1 0xff
                  EXP
                  PUSH1 0x3
                  SSTORE
                  PUSH1 0x20
                  PUSH1 0xff
                  EXP
                  PUSH1 0xff
                  EXP
                  PUSH1 0x4
                  SSTORE
                  PUSH1 0x20
                  PUSH2 0x101
                  EXP
                  PUSH1 0xff
                  EXP
                  PUSH1 0x5
                  SSTORE
                  PUSH1 0x20
                  PUSH2 0x100
                  EXP
                  PUSH2 0x101
                  EXP
                  PUSH1 0x6
                  SSTORE
                  PUSH1 0x20
                  PUSH1 0xff
                  EXP
                  PUSH2 0x101
                  EXP
                  PUSH1 0x7
                  SSTORE
                  PUSH1 0x20
                  PUSH2 0x101
                  EXP
                  PUSH2 0x101
                  EXP
                  PUSH1 0x8
                  SSTORE
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
        gaslimit = 10000000
        world = evm.EVMWorld(
            constraints,
            blocknumber=blocknumber,
            timestamp=timestamp,
            difficulty=difficulty,
            coinbase=coinbase,
            gaslimit=gaslimit,
        )

        acc_addr = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        acc_code = unhexlify(
            "60206101000a6101000a600055602060ff0a6101000a60015560206101010a6101000a60025560206101000a60ff0a600355602060ff0a60ff0a60045560206101010a60ff0a60055560206101000a6101010a600655602060ff0a6101010a60075560206101010a6101010a600855"
        )
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F2947DEF4CF144679DA39C4C32BDC35681
        price = 0x5AF3107A4000
        value = 1000000000000000000
        gas = 1000000
        data = ""
        # open a fake tx, no funds send
        world._open_transaction("CALL", address, price, data, caller, value, gas=gas)

        # This variable might seem redundant in some tests - don't forget it is auto generated
        # and there are cases in which we need it ;)
        result, returndata = self._test_run(world)

        # World sanity checks - those should not change, right?
        self.assertEqual(solve(world.block_number()), 0)
        self.assertEqual(solve(world.block_gaslimit()), 10000000)
        self.assertEqual(solve(world.block_timestamp()), 1)
        self.assertEqual(solve(world.block_difficulty()), 256)
        self.assertEqual(solve(world.block_coinbase()), 0x2ADC25665018AA1FE0E6BC666DAC8FC2697FF9BA)

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 0)
        self.assertEqual(
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 1000000000000000000
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6),
            unhexlify(
                "60206101000a6101000a600055602060ff0a6101000a60015560206101010a6101000a60025560206101000a60ff0a600355602060ff0a60ff0a60045560206101010a60ff0a60055560206101000a6101010a600655602060ff0a6101010a60075560206101010a6101010a600855"
            ),
        )
        # check storage
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x00)), 0x01
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x03)), 0x01
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x04)),
            0xB8247842BB5CE75C08D0C251669ED5870FA24A22952E5DB3A7C66C59FFE000FF,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x05)),
            0xEE526E5A06F2A990B2BF6C951E5FEABF0E07EE16877296E1BE872DB9E02000FF,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x06)), 0x01
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x07)),
            0xEDA7D024B6DE40A9D3B966E71F10A4667EDC5B71CAB07AEABCAC6249DFE00101,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x08)),
            0x512ECFAEEB11205F0833E1054DCB1300488E0954BE5AF77A49E143AA00200101,
        )
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
        self.assertEqual(solve(world.current_vm.gas), 847702)

    def test_expPowerOf256_20(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: expPowerOf256_20.json
        sha256sum: b0740a6ca31abb6604729d5c5904c1c79842624834b8c01a0b3dfec6c470313e
        Code:     PUSH1 0x14
                  PUSH2 0x100
                  EXP
                  PUSH1 0x0
                  SSTORE
                  PUSH1 0x14
                  PUSH1 0xff
                  EXP
                  PUSH1 0x1
                  SSTORE
                  PUSH1 0x14
                  PUSH2 0x101
                  EXP
                  PUSH1 0x2
                  SSTORE
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
        acc_code = unhexlify("60146101000a600055601460ff0a60015560146101010a600255")
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F2947DEF4CF144679DA39C4C32BDC35681
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

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 0)
        self.assertEqual(
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 1000000000000000000
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6),
            unhexlify("60146101000a600055601460ff0a60015560146101010a600255"),
        )
        # check storage
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x00)),
            0x010000000000000000000000000000000000000000,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x01)),
            0xECB99EB1063B1984B725D2E3C72B82E88CBDEC01,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x02)),
            0x0114C2872A2898BEA4EC46054167A4A2F174BE1401,
        )
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
        self.assertEqual(solve(world.current_vm.gas), 39913)

    def test_sdiv_i256min3(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: sdiv_i256min3.json
        sha256sum: 353f04f71f36a087f355ba9def055b57d53c65fcb2ebb9890dee44ffd6f0e105
        Code:     PUSH32 0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
                  PUSH1 0x0
                  SUB
                  PUSH32 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
                  SDIV
                  PUSH1 0x0
                  SSTORE
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
        acc_code = unhexlify(
            "7f7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff6000037fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff05600055"
        )
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F2947DEF4CF144679DA39C4C32BDC35681
        price = 0x1
        value = 1000000000000000000
        gas = 1000000
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

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 0)
        self.assertEqual(
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 1000000000000000000
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6),
            unhexlify(
                "7f7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff6000037fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff05600055"
            ),
        )
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
        self.assertEqual(solve(world.current_vm.gas), 994980)

    def test_not1(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: not1.json
        sha256sum: 13cf83235d5f2f14e56adcbbe92abdd7486d880792d166f951a4f43bd36e2898
        Code:     PUSH3 0x1e240
                  PUSH1 0x0
                  MSTORE
                  PUSH1 0x0
                  MLOAD
                  NOT
                  PUSH1 0x0
                  MSTORE
                  PUSH1 0x20
                  PUSH1 0x0
                  RETURN
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
        gaslimit = 10000000
        world = evm.EVMWorld(
            constraints,
            blocknumber=blocknumber,
            timestamp=timestamp,
            difficulty=difficulty,
            coinbase=coinbase,
            gaslimit=gaslimit,
        )

        acc_addr = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        acc_code = unhexlify("6201e2406000526000511960005260206000f3")
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F2947DEF4CF144679DA39C4C32BDC35681
        price = 0x5AF3107A4000
        value = 1000000000000000000
        gas = 1000000
        data = ""
        # open a fake tx, no funds send
        world._open_transaction("CALL", address, price, data, caller, value, gas=gas)

        # This variable might seem redundant in some tests - don't forget it is auto generated
        # and there are cases in which we need it ;)
        result, returndata = self._test_run(world)

        # World sanity checks - those should not change, right?
        self.assertEqual(solve(world.block_number()), 0)
        self.assertEqual(solve(world.block_gaslimit()), 10000000)
        self.assertEqual(solve(world.block_timestamp()), 1)
        self.assertEqual(solve(world.block_difficulty()), 256)
        self.assertEqual(solve(world.block_coinbase()), 0x2ADC25665018AA1FE0E6BC666DAC8FC2697FF9BA)

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 0)
        self.assertEqual(
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 1000000000000000000
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6),
            unhexlify("6201e2406000526000511960005260206000f3"),
        )
        # check outs
        self.assertEqual(
            returndata,
            unhexlify("fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe1dbf"),
        )
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
        self.assertEqual(solve(world.current_vm.gas), 999967)

    def test_sdiv5(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: sdiv5.json
        sha256sum: 024224e1f6e953cab5d5c8c00eb01e65eaba45104cce696fa37b6f1304676e6c
        Code:     PUSH1 0x1
                  PUSH1 0x0
                  SUB
                  PUSH32 0x8000000000000000000000000000000000000000000000000000000000000000
                  PUSH1 0x0
                  SUB
                  SDIV
                  PUSH1 0x0
                  SSTORE
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
        acc_code = unhexlify(
            "60016000037f800000000000000000000000000000000000000000000000000000000000000060000305600055"
        )
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F2947DEF4CF144679DA39C4C32BDC35681
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

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 0)
        self.assertEqual(
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 1000000000000000000
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6),
            unhexlify(
                "60016000037f800000000000000000000000000000000000000000000000000000000000000060000305600055"
            ),
        )
        # check storage
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x00)),
            0x8000000000000000000000000000000000000000000000000000000000000000,
        )
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
        self.assertEqual(solve(world.current_vm.gas), 79974)

    def test_signextendInvalidByteNumber(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: signextendInvalidByteNumber.json
        sha256sum: 7c8bbd8aaa7686a5d5644055eccba627e669859acd3f86370244ea4cfdd86bcf
        Code:     PUSH3 0x126af4
                  PUSH1 0x50
                  SIGNEXTEND
                  PUSH1 0x0
                  SSTORE
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
        gaslimit = 10000000
        world = evm.EVMWorld(
            constraints,
            blocknumber=blocknumber,
            timestamp=timestamp,
            difficulty=difficulty,
            coinbase=coinbase,
            gaslimit=gaslimit,
        )

        acc_addr = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        acc_code = unhexlify("62126af460500b600055")
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F2947DEF4CF144679DA39C4C32BDC35681
        price = 0x5AF3107A4000
        value = 1000000000000000000
        gas = 1000000
        data = ""
        # open a fake tx, no funds send
        world._open_transaction("CALL", address, price, data, caller, value, gas=gas)

        # This variable might seem redundant in some tests - don't forget it is auto generated
        # and there are cases in which we need it ;)
        result, returndata = self._test_run(world)

        # World sanity checks - those should not change, right?
        self.assertEqual(solve(world.block_number()), 0)
        self.assertEqual(solve(world.block_gaslimit()), 10000000)
        self.assertEqual(solve(world.block_timestamp()), 1)
        self.assertEqual(solve(world.block_difficulty()), 256)
        self.assertEqual(solve(world.block_coinbase()), 0x2ADC25665018AA1FE0E6BC666DAC8FC2697FF9BA)

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 0)
        self.assertEqual(
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 1000000000000000000
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6),
            unhexlify("62126af460500b600055"),
        )
        # check storage
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x00)), 0x126AF4
        )
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
        self.assertEqual(solve(world.current_vm.gas), 979986)

    def test_expPowerOf256_9(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: expPowerOf256_9.json
        sha256sum: d86d61b53ef010f8122ef525d1d4662b9b6a680256aebca4630918e07de611f0
        Code:     PUSH1 0x9
                  PUSH2 0x100
                  EXP
                  PUSH1 0x0
                  SSTORE
                  PUSH1 0x9
                  PUSH1 0xff
                  EXP
                  PUSH1 0x1
                  SSTORE
                  PUSH1 0x9
                  PUSH2 0x101
                  EXP
                  PUSH1 0x2
                  SSTORE
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
        acc_code = unhexlify("60096101000a600055600960ff0a60015560096101010a600255")
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F2947DEF4CF144679DA39C4C32BDC35681
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

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 0)
        self.assertEqual(
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 1000000000000000000
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6),
            unhexlify("60096101000a600055600960ff0a60015560096101010a600255"),
        )
        # check storage
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x00)),
            0x01000000000000000000,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x01)),
            0xF723AC7D8253DC08FF,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x02)),
            0x010924547E7E54240901,
        )
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
        self.assertEqual(solve(world.current_vm.gas), 39913)

    def test_expPowerOf256_8(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: expPowerOf256_8.json
        sha256sum: 9f8782ad28deabc9d357679318ddc65c1fd930005800b8431dc204ebd574e98b
        Code:     PUSH1 0x8
                  PUSH2 0x100
                  EXP
                  PUSH1 0x0
                  SSTORE
                  PUSH1 0x8
                  PUSH1 0xff
                  EXP
                  PUSH1 0x1
                  SSTORE
                  PUSH1 0x8
                  PUSH2 0x101
                  EXP
                  PUSH1 0x2
                  SSTORE
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
        acc_code = unhexlify("60086101000a600055600860ff0a60015560086101010a600255")
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F2947DEF4CF144679DA39C4C32BDC35681
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

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 0)
        self.assertEqual(
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 1000000000000000000
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6),
            unhexlify("60086101000a600055600860ff0a60015560086101010a600255"),
        )
        # check storage
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x00)),
            0x010000000000000000,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x01)),
            0xF81BC845C81BF801,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x02)),
            0x01081C3846381C0801,
        )
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
        self.assertEqual(solve(world.current_vm.gas), 39913)

    def test_divByNonZero3(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: divByNonZero3.json
        sha256sum: 9b1768e48871638a195e9d85141a0fd5b85e3478597ff05f85ca883ccc9c83d4
        Code:     PUSH1 0x1
                  PUSH1 0x1
                  DIV
                  PUSH1 0x0
                  SSTORE
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
        acc_code = unhexlify("6001600104600055")
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F2947DEF4CF144679DA39C4C32BDC35681
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

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 0)
        self.assertEqual(
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 1000000000000000000
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6), unhexlify("6001600104600055")
        )
        # check storage
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x00)), 0x01
        )
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
        self.assertEqual(solve(world.current_vm.gas), 79986)

    def test_expPowerOf256_12(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: expPowerOf256_12.json
        sha256sum: 6961b8ed41be6fab3df3b7ad24004c9513c69ecd51a80f3a54d8f3f0c3598de2
        Code:     PUSH1 0xc
                  PUSH2 0x100
                  EXP
                  PUSH1 0x0
                  SSTORE
                  PUSH1 0xc
                  PUSH1 0xff
                  EXP
                  PUSH1 0x1
                  SSTORE
                  PUSH1 0xc
                  PUSH2 0x101
                  EXP
                  PUSH1 0x2
                  SSTORE
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
        acc_code = unhexlify("600c6101000a600055600c60ff0a600155600c6101010a600255")
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F2947DEF4CF144679DA39C4C32BDC35681
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

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 0)
        self.assertEqual(
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 1000000000000000000
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6),
            unhexlify("600c6101000a600055600c60ff0a600155600c6101010a600255"),
        )
        # check storage
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x00)),
            0x01000000000000000000000000,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x01)),
            0xF44125EBEB98E9EE2441F401,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x02)),
            0x010C42DDF21B9F19EFDC420C01,
        )
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
        self.assertEqual(solve(world.current_vm.gas), 39913)

    def test_expPowerOf256Of256_21(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: expPowerOf256Of256_21.json
        sha256sum: 133b198b7d5f401a7c9e8f06f60743ed28a5fd8bf385d818423fd2c634b10e86
        Code:     PUSH1 0x15
                  PUSH2 0x100
                  EXP
                  PUSH2 0x100
                  EXP
                  PUSH1 0x0
                  SSTORE
                  PUSH1 0x15
                  PUSH1 0xff
                  EXP
                  PUSH2 0x100
                  EXP
                  PUSH1 0x1
                  SSTORE
                  PUSH1 0x15
                  PUSH2 0x101
                  EXP
                  PUSH2 0x100
                  EXP
                  PUSH1 0x2
                  SSTORE
                  PUSH1 0x15
                  PUSH2 0x100
                  EXP
                  PUSH1 0xff
                  EXP
                  PUSH1 0x3
                  SSTORE
                  PUSH1 0x15
                  PUSH1 0xff
                  EXP
                  PUSH1 0xff
                  EXP
                  PUSH1 0x4
                  SSTORE
                  PUSH1 0x15
                  PUSH2 0x101
                  EXP
                  PUSH1 0xff
                  EXP
                  PUSH1 0x5
                  SSTORE
                  PUSH1 0x15
                  PUSH2 0x100
                  EXP
                  PUSH2 0x101
                  EXP
                  PUSH1 0x6
                  SSTORE
                  PUSH1 0x15
                  PUSH1 0xff
                  EXP
                  PUSH2 0x101
                  EXP
                  PUSH1 0x7
                  SSTORE
                  PUSH1 0x15
                  PUSH2 0x101
                  EXP
                  PUSH2 0x101
                  EXP
                  PUSH1 0x8
                  SSTORE
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
        gaslimit = 10000000
        world = evm.EVMWorld(
            constraints,
            blocknumber=blocknumber,
            timestamp=timestamp,
            difficulty=difficulty,
            coinbase=coinbase,
            gaslimit=gaslimit,
        )

        acc_addr = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        acc_code = unhexlify(
            "60156101000a6101000a600055601560ff0a6101000a60015560156101010a6101000a60025560156101000a60ff0a600355601560ff0a60ff0a60045560156101010a60ff0a60055560156101000a6101010a600655601560ff0a6101010a60075560156101010a6101010a600855"
        )
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F2947DEF4CF144679DA39C4C32BDC35681
        price = 0x5AF3107A4000
        value = 1000000000000000000
        gas = 1000000
        data = ""
        # open a fake tx, no funds send
        world._open_transaction("CALL", address, price, data, caller, value, gas=gas)

        # This variable might seem redundant in some tests - don't forget it is auto generated
        # and there are cases in which we need it ;)
        result, returndata = self._test_run(world)

        # World sanity checks - those should not change, right?
        self.assertEqual(solve(world.block_number()), 0)
        self.assertEqual(solve(world.block_gaslimit()), 10000000)
        self.assertEqual(solve(world.block_timestamp()), 1)
        self.assertEqual(solve(world.block_difficulty()), 256)
        self.assertEqual(solve(world.block_coinbase()), 0x2ADC25665018AA1FE0E6BC666DAC8FC2697FF9BA)

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 0)
        self.assertEqual(
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 1000000000000000000
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6),
            unhexlify(
                "60156101000a6101000a600055601560ff0a6101000a60015560156101010a6101000a60025560156101000a60ff0a600355601560ff0a60ff0a60045560156101010a60ff0a60055560156101000a6101010a600655601560ff0a6101010a60075560156101010a6101010a600855"
            ),
        )
        # check storage
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x03)),
            0x879EC55C33085514FF7F00000000000000000000000000000000000000000001,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x04)),
            0x7FD07055FF50CDFE4B4BD9A15133D72D3607D92EB7AC81BAC93DB7FF4C93FEFF,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x05)),
            0x665AC5C769E87F61D5993ABC26522FBFCA2734D76A63216B2D550D29C79500FF,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x06)),
            0xB68FB921F7AA6AFF8100000000000000000000000000000000000000000001,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x07)),
            0x1C93DB67C9884BC694686D69A25A5D7ED089841D5CE147FDD7199AB00D95FF01,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x08)),
            0x485053D8FF66BE52036597520344FAC87B6A305426A9E49221D3F934DC950101,
        )
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
        self.assertEqual(solve(world.current_vm.gas), 862672)

    def test_expPowerOf256Of256_17(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: expPowerOf256Of256_17.json
        sha256sum: efdafd61b4d2430c56294205b0389c494d8d35733419d89e2189884ec84ffb0e
        Code:     PUSH1 0x11
                  PUSH2 0x100
                  EXP
                  PUSH2 0x100
                  EXP
                  PUSH1 0x0
                  SSTORE
                  PUSH1 0x11
                  PUSH1 0xff
                  EXP
                  PUSH2 0x100
                  EXP
                  PUSH1 0x1
                  SSTORE
                  PUSH1 0x11
                  PUSH2 0x101
                  EXP
                  PUSH2 0x100
                  EXP
                  PUSH1 0x2
                  SSTORE
                  PUSH1 0x11
                  PUSH2 0x100
                  EXP
                  PUSH1 0xff
                  EXP
                  PUSH1 0x3
                  SSTORE
                  PUSH1 0x11
                  PUSH1 0xff
                  EXP
                  PUSH1 0xff
                  EXP
                  PUSH1 0x4
                  SSTORE
                  PUSH1 0x11
                  PUSH2 0x101
                  EXP
                  PUSH1 0xff
                  EXP
                  PUSH1 0x5
                  SSTORE
                  PUSH1 0x11
                  PUSH2 0x100
                  EXP
                  PUSH2 0x101
                  EXP
                  PUSH1 0x6
                  SSTORE
                  PUSH1 0x11
                  PUSH1 0xff
                  EXP
                  PUSH2 0x101
                  EXP
                  PUSH1 0x7
                  SSTORE
                  PUSH1 0x11
                  PUSH2 0x101
                  EXP
                  PUSH2 0x101
                  EXP
                  PUSH1 0x8
                  SSTORE
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
        gaslimit = 10000000
        world = evm.EVMWorld(
            constraints,
            blocknumber=blocknumber,
            timestamp=timestamp,
            difficulty=difficulty,
            coinbase=coinbase,
            gaslimit=gaslimit,
        )

        acc_addr = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        acc_code = unhexlify(
            "60116101000a6101000a600055601160ff0a6101000a60015560116101010a6101000a60025560116101000a60ff0a600355601160ff0a60ff0a60045560116101010a60ff0a60055560116101000a6101010a600655601160ff0a6101010a60075560116101010a6101010a600855"
        )
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F2947DEF4CF144679DA39C4C32BDC35681
        price = 0x5AF3107A4000
        value = 1000000000000000000
        gas = 1000000
        data = ""
        # open a fake tx, no funds send
        world._open_transaction("CALL", address, price, data, caller, value, gas=gas)

        # This variable might seem redundant in some tests - don't forget it is auto generated
        # and there are cases in which we need it ;)
        result, returndata = self._test_run(world)

        # World sanity checks - those should not change, right?
        self.assertEqual(solve(world.block_number()), 0)
        self.assertEqual(solve(world.block_gaslimit()), 10000000)
        self.assertEqual(solve(world.block_timestamp()), 1)
        self.assertEqual(solve(world.block_difficulty()), 256)
        self.assertEqual(solve(world.block_coinbase()), 0x2ADC25665018AA1FE0E6BC666DAC8FC2697FF9BA)

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 0)
        self.assertEqual(
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 1000000000000000000
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6),
            unhexlify(
                "60116101000a6101000a600055601160ff0a6101000a60015560116101010a6101000a60025560116101000a60ff0a600355601160ff0a60ff0a60045560116101010a60ff0a60055560116101000a6101010a600655601160ff0a6101010a60075560116101010a6101010a600855"
            ),
        )
        # check storage
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x03)),
            0xEC698218879EC55C33085514FF7F000000000000000000000000000000000001,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x04)),
            0x722AD218EB1995A2D257C4C06D8DE993C203CFC8E3512DF7D633E17E908FFEFF,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x05)),
            0x8AC9B5EC08D74612CB29F941481D274B51721AF2296207C0DA8D24667F9100FF,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x06)),
            0x8FC9B0F000B68FB921F7AA6AFF81000000000000000000000000000000000001,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x07)),
            0x81D5FF63680841482299F3EAB616446DCD336F537C0C565AA4112AB95D91FF01,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x08)),
            0x9C6CA90DAC4E97DEA02AC969E8649EE9E6232E0C3F4797411151CB8F90910101,
        )
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
        self.assertEqual(solve(world.current_vm.gas), 863032)

    def test_mul0(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: mul0.json
        sha256sum: 33b2ee01c056d260f630ce5fef98c68a54c3e4bbf64352acee459726de2a4124
        Code:     PUSH1 0x3
                  PUSH1 0x2
                  MUL
                  PUSH1 0x0
                  SSTORE
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
        acc_code = unhexlify("6003600202600055")
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F2947DEF4CF144679DA39C4C32BDC35681
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

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 0)
        self.assertEqual(
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 1000000000000000000
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6), unhexlify("6003600202600055")
        )
        # check storage
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x00)), 0x06
        )
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
        self.assertEqual(solve(world.current_vm.gas), 79986)

    def test_addmod3(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: addmod3.json
        sha256sum: e5b07da689ffac562e99efc151d2c9e85f8ec9d86b0a232c66722f0ed279ef47
        Code:     PUSH1 0x3
                  PUSH1 0x0
                  SUB
                  PUSH1 0x1
                  PUSH1 0x4
                  ADDMOD
                  PUSH1 0x0
                  SSTORE
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
        acc_code = unhexlify("60036000036001600408600055")
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F2947DEF4CF144679DA39C4C32BDC35681
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

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 0)
        self.assertEqual(
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 1000000000000000000
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6),
            unhexlify("60036000036001600408600055"),
        )
        # check storage
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x00)), 0x05
        )
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
        self.assertEqual(solve(world.current_vm.gas), 79974)

    def test_sdivByZero2(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: sdivByZero2.json
        sha256sum: 3f978fa1b9337f8832324811fdd45fb9d6a5dc7034afebba9a7c909c223f78dc
        Code:     PUSH1 0x1
                  PUSH1 0x0
                  PUSH32 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffcf923bdff
                  PUSH1 0x0
                  SUB
                  SDIV
                  ADD
                  PUSH1 0x0
                  SSTORE
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
        acc_code = unhexlify(
            "600160007ffffffffffffffffffffffffffffffffffffffffffffffffffffffffcf923bdff6000030501600055"
        )
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F2947DEF4CF144679DA39C4C32BDC35681
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

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 0)
        self.assertEqual(
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 1000000000000000000
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6),
            unhexlify(
                "600160007ffffffffffffffffffffffffffffffffffffffffffffffffffffffffcf923bdff6000030501600055"
            ),
        )
        # check storage
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x00)), 0x01
        )
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
        self.assertEqual(solve(world.current_vm.gas), 79974)

    def test_expPowerOf256_17(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: expPowerOf256_17.json
        sha256sum: 2a3ef1239a77968bac4ef2b4def123cb9d5390fdbecd1b2924c7a77fbb47cba1
        Code:     PUSH1 0x11
                  PUSH2 0x100
                  EXP
                  PUSH1 0x0
                  SSTORE
                  PUSH1 0x11
                  PUSH1 0xff
                  EXP
                  PUSH1 0x1
                  SSTORE
                  PUSH1 0x11
                  PUSH2 0x101
                  EXP
                  PUSH1 0x2
                  SSTORE
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
        acc_code = unhexlify("60116101000a600055601160ff0a60015560116101010a600255")
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F2947DEF4CF144679DA39C4C32BDC35681
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

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 0)
        self.assertEqual(
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 1000000000000000000
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6),
            unhexlify("60116101000a600055601160ff0a60015560116101010a600255"),
        )
        # check storage
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x00)),
            0x010000000000000000000000000000000000,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x01)),
            0xEF856134040C669755C7C022B6A77810FF,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x02)),
            0x01118AB1645CA45755422870354EA8881101,
        )
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
        self.assertEqual(solve(world.current_vm.gas), 39913)

    def test_expPowerOf256_26(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: expPowerOf256_26.json
        sha256sum: 6ae8556c5859ce81eae1c2315b6b14d3d081bea3d4fb901a3269943ac05da3c6
        Code:     PUSH1 0x1a
                  PUSH2 0x100
                  EXP
                  PUSH1 0x0
                  SSTORE
                  PUSH1 0x1a
                  PUSH1 0xff
                  EXP
                  PUSH1 0x1
                  SSTORE
                  PUSH1 0x1a
                  PUSH2 0x101
                  EXP
                  PUSH1 0x2
                  SSTORE
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
        acc_code = unhexlify("601a6101000a600055601a60ff0a600155601a6101010a600255")
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F2947DEF4CF144679DA39C4C32BDC35681
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

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 0)
        self.assertEqual(
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 1000000000000000000
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6),
            unhexlify("601a6101000a600055601a60ff0a600155601a6101010a600255"),
        )
        # check storage
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x00)),
            0x010000000000000000000000000000000000000000000000000000,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x01)),
            0xE73B116885641F4651A56F438FD08D61869CFA55465BD944E601,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x02)),
            0x011B4F636A81778EA1C96F4CAB2B998CBC26B00C572E7029451A01,
        )
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
        self.assertEqual(solve(world.current_vm.gas), 39913)

    def test_add1(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: add1.json
        sha256sum: fab06ebfaeb71e4017dec55cd4b45472b843d9cb9001b54eb4cfceabeb5141c2
        Code:     PUSH1 0x4
                  PUSH32 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
                  ADD
                  PUSH1 0x0
                  SSTORE
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
        acc_code = unhexlify(
            "60047fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff01600055"
        )
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F2947DEF4CF144679DA39C4C32BDC35681
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

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 0)
        self.assertEqual(
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 1000000000000000000
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6),
            unhexlify(
                "60047fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff01600055"
            ),
        )
        # check storage
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x00)), 0x03
        )
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
        self.assertEqual(solve(world.current_vm.gas), 79988)

    def test_exp4(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: exp4.json
        sha256sum: b0afd80d0882556ef89a57269e89616dd8f3eb5b0b97c5c2505f36415fc643cd
        Code:     PUSH1 0x0
                  PUSH4 0x7fffffff
                  EXP
                  PUSH1 0x0
                  SSTORE
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
        acc_code = unhexlify("6000637fffffff0a600055")
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F2947DEF4CF144679DA39C4C32BDC35681
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

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 0)
        self.assertEqual(
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 1000000000000000000
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6),
            unhexlify("6000637fffffff0a600055"),
        )
        # check storage
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x00)), 0x01
        )
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
        self.assertEqual(solve(world.current_vm.gas), 79981)

    def test_sub1(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: sub1.json
        sha256sum: 738dccff9466ec1fc4f88b7e7387cba994042be68f37e47ffd3bef90d5e360cd
        Code:     PUSH1 0x3
                  PUSH1 0x2
                  SUB
                  PUSH1 0x0
                  SSTORE
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
        acc_code = unhexlify("6003600203600055")
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F2947DEF4CF144679DA39C4C32BDC35681
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

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 0)
        self.assertEqual(
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 1000000000000000000
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6), unhexlify("6003600203600055")
        )
        # check storage
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x00)),
            0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF,
        )
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
        self.assertEqual(solve(world.current_vm.gas), 79988)

    def test_expPowerOf2_4(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: expPowerOf2_4.json
        sha256sum: e3f55c2e3267c73c4125fec63c1f6b90ce6ad5d2117ce695f71eef6a6e6176df
        Code:     PUSH1 0x4
                  PUSH1 0x2
                  EXP
                  PUSH1 0x0
                  SSTORE
                  PUSH1 0x3
                  PUSH1 0x2
                  EXP
                  PUSH1 0x1
                  SSTORE
                  PUSH1 0x5
                  PUSH1 0x2
                  EXP
                  PUSH1 0x2
                  SSTORE
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
        acc_code = unhexlify("600460020a600055600360020a600155600560020a600255")
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F2947DEF4CF144679DA39C4C32BDC35681
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

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 0)
        self.assertEqual(
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 1000000000000000000
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6),
            unhexlify("600460020a600055600360020a600155600560020a600255"),
        )
        # check storage
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x00)), 0x10
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x01)), 0x08
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x02)), 0x20
        )
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
        self.assertEqual(solve(world.current_vm.gas), 39913)

    def test_sdiv9(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: sdiv9.json
        sha256sum: ca75fe70e645e1c0b6b5ca6586f4f084300f5247ca8c78e0e7c57b9c3f4115a4
        Code:     PUSH1 0x1
                  PUSH1 0x1
                  PUSH1 0x0
                  SUB
                  SDIV
                  PUSH1 0x0
                  SSTORE
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
        acc_code = unhexlify("6001600160000305600055")
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F2947DEF4CF144679DA39C4C32BDC35681
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

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 0)
        self.assertEqual(
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 1000000000000000000
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6),
            unhexlify("6001600160000305600055"),
        )
        # check storage
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x00)),
            0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF,
        )
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
        self.assertEqual(solve(world.current_vm.gas), 79980)

    def test_expPowerOf256_19(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: expPowerOf256_19.json
        sha256sum: 0cc1c1acafa265d5699e932898535330a4ae5a7da33df446d3de1bc9b8f4111e
        Code:     PUSH1 0x13
                  PUSH2 0x100
                  EXP
                  PUSH1 0x0
                  SSTORE
                  PUSH1 0x13
                  PUSH1 0xff
                  EXP
                  PUSH1 0x1
                  SSTORE
                  PUSH1 0x13
                  PUSH2 0x101
                  EXP
                  PUSH1 0x2
                  SSTORE
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
        acc_code = unhexlify("60136101000a600055601360ff0a60015560136101010a600255")
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F2947DEF4CF144679DA39C4C32BDC35681
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

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 0)
        self.assertEqual(
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 1000000000000000000
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6),
            unhexlify("60136101000a600055601360ff0a60015560136101010a600255"),
        )
        # check storage
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x00)),
            0x0100000000000000000000000000000000000000,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x01)),
            0xEDA745F6FD3851D68DB3866A315CDFC85512FF,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x02)),
            0x0113AED851D6C1FCA84402033E297B27C9AB1301,
        )
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
        self.assertEqual(solve(world.current_vm.gas), 39913)

    def test_expPowerOf256Of256_29(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: expPowerOf256Of256_29.json
        sha256sum: 7e5cd980778372fddd4fe5da72d58a03f7248ea522d4ff1cee8774289648dd19
        Code:     PUSH1 0x1d
                  PUSH2 0x100
                  EXP
                  PUSH2 0x100
                  EXP
                  PUSH1 0x0
                  SSTORE
                  PUSH1 0x1d
                  PUSH1 0xff
                  EXP
                  PUSH2 0x100
                  EXP
                  PUSH1 0x1
                  SSTORE
                  PUSH1 0x1d
                  PUSH2 0x101
                  EXP
                  PUSH2 0x100
                  EXP
                  PUSH1 0x2
                  SSTORE
                  PUSH1 0x1d
                  PUSH2 0x100
                  EXP
                  PUSH1 0xff
                  EXP
                  PUSH1 0x3
                  SSTORE
                  PUSH1 0x1d
                  PUSH1 0xff
                  EXP
                  PUSH1 0xff
                  EXP
                  PUSH1 0x4
                  SSTORE
                  PUSH1 0x1d
                  PUSH2 0x101
                  EXP
                  PUSH1 0xff
                  EXP
                  PUSH1 0x5
                  SSTORE
                  PUSH1 0x1d
                  PUSH2 0x100
                  EXP
                  PUSH2 0x101
                  EXP
                  PUSH1 0x6
                  SSTORE
                  PUSH1 0x1d
                  PUSH1 0xff
                  EXP
                  PUSH2 0x101
                  EXP
                  PUSH1 0x7
                  SSTORE
                  PUSH1 0x1d
                  PUSH2 0x101
                  EXP
                  PUSH2 0x101
                  EXP
                  PUSH1 0x8
                  SSTORE
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
        gaslimit = 10000000
        world = evm.EVMWorld(
            constraints,
            blocknumber=blocknumber,
            timestamp=timestamp,
            difficulty=difficulty,
            coinbase=coinbase,
            gaslimit=gaslimit,
        )

        acc_addr = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        acc_code = unhexlify(
            "601d6101000a6101000a600055601d60ff0a6101000a600155601d6101010a6101000a600255601d6101000a60ff0a600355601d60ff0a60ff0a600455601d6101010a60ff0a600555601d6101000a6101010a600655601d60ff0a6101010a600755601d6101010a6101010a600855"
        )
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F2947DEF4CF144679DA39C4C32BDC35681
        price = 0x5AF3107A4000
        value = 1000000000000000000
        gas = 1000000
        data = ""
        # open a fake tx, no funds send
        world._open_transaction("CALL", address, price, data, caller, value, gas=gas)

        # This variable might seem redundant in some tests - don't forget it is auto generated
        # and there are cases in which we need it ;)
        result, returndata = self._test_run(world)

        # World sanity checks - those should not change, right?
        self.assertEqual(solve(world.block_number()), 0)
        self.assertEqual(solve(world.block_gaslimit()), 10000000)
        self.assertEqual(solve(world.block_timestamp()), 1)
        self.assertEqual(solve(world.block_difficulty()), 256)
        self.assertEqual(solve(world.block_coinbase()), 0x2ADC25665018AA1FE0E6BC666DAC8FC2697FF9BA)

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 0)
        self.assertEqual(
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 1000000000000000000
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6),
            unhexlify(
                "601d6101000a6101000a600055601d60ff0a6101000a600155601d6101010a6101000a600255601d6101000a60ff0a600355601d60ff0a60ff0a600455601d6101010a60ff0a600555601d6101000a6101010a600655601d60ff0a6101010a600755601d6101010a6101010a600855"
            ),
        )
        # check storage
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x03)),
            0xFF7F000000000000000000000000000000000000000000000000000000000001,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x04)),
            0x41E065D46E0349CFE624C4E8A2034AEA1F7EDFFF80E511CD8067D488949BFEFF,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x05)),
            0xA84162CA6675A22C4C79DFC4EA15F760DB5A04DBF04246764199B668879D00FF,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x06)),
            0xFF81000000000000000000000000000000000000000000000000000000000001,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x07)),
            0x1226984FAA6B05EBDBD45D8477FA4FD5B55BFD5061DE03C319282B153D9DFF01,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x08)),
            0x5CC9E6B0B749FD94541AD00364BDEC2FCA7816981CA3E38F485DECC7A49D0101,
        )
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
        self.assertEqual(solve(world.current_vm.gas), 861952)

    def test_expPowerOf256Of256_5(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: expPowerOf256Of256_5.json
        sha256sum: e52f4cbdddf85ea945200f2b9aa9ebd3c0fa2359394022c188149b9fe18a132f
        Code:     PUSH1 0x5
                  PUSH2 0x100
                  EXP
                  PUSH2 0x100
                  EXP
                  PUSH1 0x0
                  SSTORE
                  PUSH1 0x5
                  PUSH1 0xff
                  EXP
                  PUSH2 0x100
                  EXP
                  PUSH1 0x1
                  SSTORE
                  PUSH1 0x5
                  PUSH2 0x101
                  EXP
                  PUSH2 0x100
                  EXP
                  PUSH1 0x2
                  SSTORE
                  PUSH1 0x5
                  PUSH2 0x100
                  EXP
                  PUSH1 0xff
                  EXP
                  PUSH1 0x3
                  SSTORE
                  PUSH1 0x5
                  PUSH1 0xff
                  EXP
                  PUSH1 0xff
                  EXP
                  PUSH1 0x4
                  SSTORE
                  PUSH1 0x5
                  PUSH2 0x101
                  EXP
                  PUSH1 0xff
                  EXP
                  PUSH1 0x5
                  SSTORE
                  PUSH1 0x5
                  PUSH2 0x100
                  EXP
                  PUSH2 0x101
                  EXP
                  PUSH1 0x6
                  SSTORE
                  PUSH1 0x5
                  PUSH1 0xff
                  EXP
                  PUSH2 0x101
                  EXP
                  PUSH1 0x7
                  SSTORE
                  PUSH1 0x5
                  PUSH2 0x101
                  EXP
                  PUSH2 0x101
                  EXP
                  PUSH1 0x8
                  SSTORE
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
        gaslimit = 10000000
        world = evm.EVMWorld(
            constraints,
            blocknumber=blocknumber,
            timestamp=timestamp,
            difficulty=difficulty,
            coinbase=coinbase,
            gaslimit=gaslimit,
        )

        acc_addr = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        acc_code = unhexlify(
            "60056101000a6101000a600055600560ff0a6101000a60015560056101010a6101000a60025560056101000a60ff0a600355600560ff0a60ff0a60045560056101010a60ff0a60055560056101000a6101010a600655600560ff0a6101010a60075560056101010a6101010a600855"
        )
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F2947DEF4CF144679DA39C4C32BDC35681
        price = 0x5AF3107A4000
        value = 1000000000000000000
        gas = 1000000
        data = ""
        # open a fake tx, no funds send
        world._open_transaction("CALL", address, price, data, caller, value, gas=gas)

        # This variable might seem redundant in some tests - don't forget it is auto generated
        # and there are cases in which we need it ;)
        result, returndata = self._test_run(world)

        # World sanity checks - those should not change, right?
        self.assertEqual(solve(world.block_number()), 0)
        self.assertEqual(solve(world.block_gaslimit()), 10000000)
        self.assertEqual(solve(world.block_timestamp()), 1)
        self.assertEqual(solve(world.block_difficulty()), 256)
        self.assertEqual(solve(world.block_coinbase()), 0x2ADC25665018AA1FE0E6BC666DAC8FC2697FF9BA)

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 0)
        self.assertEqual(
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 1000000000000000000
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6),
            unhexlify(
                "60056101000a6101000a600055600560ff0a6101000a60015560056101010a6101000a60025560056101000a60ff0a600355600560ff0a60ff0a60045560056101010a60ff0a60055560056101000a6101010a600655600560ff0a6101010a60075560056101010a6101010a600855"
            ),
        )
        # check storage
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x03)),
            0xB581AC185AAD71DB2D177C286929C4C22809E5DCB3085514FF7F000000000001,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x04)),
            0x75789EB2A64BC971389FBD11A1E6D7ABBF95AD25E23FB9AA25E73A0BFC83FEFF,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x05)),
            0xFC403FA42CEB6A0D0D3321BD9B2D8AF25B1B667F87A04F496C78168D078500FF,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x06)),
            0xCEC5EC213B9CB5811F6AE00428FD7B6EF5A1AF39A1F7AA6AFF81000000000001,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x07)),
            0x70AB32233202B98D382D17713FA0BE391EAF74F85BA1740C9C3238C4ED85FF01,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x08)),
            0xB622672A213FAA79B32185FF93A7B27A8499E48F7B032CDB4D1A70300C850101,
        )
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
        self.assertEqual(solve(world.current_vm.gas), 864112)

    def test_smod3(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: smod3.json
        sha256sum: b8dd5232d3daa08785f18e4265162f131a9ff7e1d052d5530aa0f7f7d1a9d212
        Code:     PUSH32 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
                  PUSH1 0x2
                  PUSH1 0x0
                  SUB
                  SMOD
                  PUSH1 0x0
                  SSTORE
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
        acc_code = unhexlify(
            "7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff600260000307600055"
        )
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F2947DEF4CF144679DA39C4C32BDC35681
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

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 0)
        self.assertEqual(
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 1000000000000000000
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6),
            unhexlify(
                "7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff600260000307600055"
            ),
        )
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
        self.assertEqual(solve(world.current_vm.gas), 94980)

    def test_mulmod1_overflow4(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: mulmod1_overflow4.json
        sha256sum: a11a3a3f24b290e9d035fde4aa7967e8a4018382a3c72799e6105d188134f573
        Code:     PUSH1 0x5
                  PUSH1 0x2
                  PUSH32 0x8000000000000000000000000000000000000000000000000000000000000001
                  MULMOD
                  PUSH1 0x0
                  SSTORE
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
        acc_code = unhexlify(
            "600560027f800000000000000000000000000000000000000000000000000000000000000109600055"
        )
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F2947DEF4CF144679DA39C4C32BDC35681
        price = 0x5AF3107A4000
        value = 1000000000000000000
        gas = 1000000
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

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 0)
        self.assertEqual(
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 1000000000000000000
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6),
            unhexlify(
                "600560027f800000000000000000000000000000000000000000000000000000000000000109600055"
            ),
        )
        # check storage
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x00)), 0x03
        )
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
        self.assertEqual(solve(world.current_vm.gas), 979980)

    def test_sdiv_i256min2(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: sdiv_i256min2.json
        sha256sum: 95b85e8b02fcb9f69748a3dcbe7b84f03a2e18d02bd9f11fa6cc81696ce117e0
        Code:     PUSH1 0x1
                  PUSH1 0x0
                  SUB
                  PUSH32 0x8000000000000000000000000000000000000000000000000000000000000000
                  PUSH1 0x0
                  SUB
                  SDIV
                  PUSH1 0x0
                  SSTORE
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
        acc_code = unhexlify(
            "60016000037f800000000000000000000000000000000000000000000000000000000000000060000305600055"
        )
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F2947DEF4CF144679DA39C4C32BDC35681
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

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 0)
        self.assertEqual(
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 1000000000000000000
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6),
            unhexlify(
                "60016000037f800000000000000000000000000000000000000000000000000000000000000060000305600055"
            ),
        )
        # check storage
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x00)),
            0x8000000000000000000000000000000000000000000000000000000000000000,
        )
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
        self.assertEqual(solve(world.current_vm.gas), 79974)

    def test_expPowerOf256_15(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: expPowerOf256_15.json
        sha256sum: 324a9bdb004fc56a3a395a7c249e5a8dacb87933c42706853dce0870c59dd1f9
        Code:     PUSH1 0xf
                  PUSH2 0x100
                  EXP
                  PUSH1 0x0
                  SSTORE
                  PUSH1 0xf
                  PUSH1 0xff
                  EXP
                  PUSH1 0x1
                  SSTORE
                  PUSH1 0xf
                  PUSH2 0x101
                  EXP
                  PUSH1 0x2
                  SSTORE
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
        acc_code = unhexlify("600f6101000a600055600f60ff0a600155600f6101010a600255")
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F2947DEF4CF144679DA39C4C32BDC35681
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

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 0)
        self.assertEqual(
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 1000000000000000000
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6),
            unhexlify("600f6101000a600055600f60ff0a600155600f6101010a600255"),
        )
        # check storage
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x00)),
            0x01000000000000000000000000000000,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x01)),
            0xF1673E495873F60F7EB5ACC6970EFF,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x02)),
            0x010F6ACC60CEA63C3698C056C7690F01,
        )
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
        self.assertEqual(solve(world.current_vm.gas), 39913)

    def test_expPowerOf256Of256_13(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: expPowerOf256Of256_13.json
        sha256sum: 3559c513219c03d76dad5cbdfb05f1a009d416fb9b0f86317e1e02adb1a50925
        Code:     PUSH1 0xd
                  PUSH2 0x100
                  EXP
                  PUSH2 0x100
                  EXP
                  PUSH1 0x0
                  SSTORE
                  PUSH1 0xd
                  PUSH1 0xff
                  EXP
                  PUSH2 0x100
                  EXP
                  PUSH1 0x1
                  SSTORE
                  PUSH1 0xd
                  PUSH2 0x101
                  EXP
                  PUSH2 0x100
                  EXP
                  PUSH1 0x2
                  SSTORE
                  PUSH1 0xd
                  PUSH2 0x100
                  EXP
                  PUSH1 0xff
                  EXP
                  PUSH1 0x3
                  SSTORE
                  PUSH1 0xd
                  PUSH1 0xff
                  EXP
                  PUSH1 0xff
                  EXP
                  PUSH1 0x4
                  SSTORE
                  PUSH1 0xd
                  PUSH2 0x101
                  EXP
                  PUSH1 0xff
                  EXP
                  PUSH1 0x5
                  SSTORE
                  PUSH1 0xd
                  PUSH2 0x100
                  EXP
                  PUSH2 0x101
                  EXP
                  PUSH1 0x6
                  SSTORE
                  PUSH1 0xd
                  PUSH1 0xff
                  EXP
                  PUSH2 0x101
                  EXP
                  PUSH1 0x7
                  SSTORE
                  PUSH1 0xd
                  PUSH2 0x101
                  EXP
                  PUSH2 0x101
                  EXP
                  PUSH1 0x8
                  SSTORE
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
        gaslimit = 10000000
        world = evm.EVMWorld(
            constraints,
            blocknumber=blocknumber,
            timestamp=timestamp,
            difficulty=difficulty,
            coinbase=coinbase,
            gaslimit=gaslimit,
        )

        acc_addr = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        acc_code = unhexlify(
            "600d6101000a6101000a600055600d60ff0a6101000a600155600d6101010a6101000a600255600d6101000a60ff0a600355600d60ff0a60ff0a600455600d6101010a60ff0a600555600d6101000a6101010a600655600d60ff0a6101010a600755600d6101010a6101010a600855"
        )
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F2947DEF4CF144679DA39C4C32BDC35681
        price = 0x5AF3107A4000
        value = 1000000000000000000
        gas = 1000000
        data = ""
        # open a fake tx, no funds send
        world._open_transaction("CALL", address, price, data, caller, value, gas=gas)

        # This variable might seem redundant in some tests - don't forget it is auto generated
        # and there are cases in which we need it ;)
        result, returndata = self._test_run(world)

        # World sanity checks - those should not change, right?
        self.assertEqual(solve(world.block_number()), 0)
        self.assertEqual(solve(world.block_gaslimit()), 10000000)
        self.assertEqual(solve(world.block_timestamp()), 1)
        self.assertEqual(solve(world.block_difficulty()), 256)
        self.assertEqual(solve(world.block_coinbase()), 0x2ADC25665018AA1FE0E6BC666DAC8FC2697FF9BA)

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 0)
        self.assertEqual(
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 1000000000000000000
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6),
            unhexlify(
                "600d6101000a6101000a600055600d60ff0a6101000a600155600d6101010a6101000a600255600d6101000a60ff0a600355600d60ff0a60ff0a600455600d6101010a60ff0a600555600d6101000a6101010a600655600d60ff0a6101010a600755600d6101010a6101010a600855"
            ),
        )
        # check storage
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x03)),
            0xE02639036C698218879EC55C33085514FF7F0000000000000000000000000001,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x04)),
            0x8BE664BDE946D939CE551B948B503787942D2A7734509288C1B62FD5C48BFEFF,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x05)),
            0xA923A28E7A75AEF26C51580FFC686879E4A0B404B089BDBCD751D88B478D00FF,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x06)),
            0x41AC5EA30FC9B0F000B68FB921F7AA6AFF810000000000000000000000000001,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x07)),
            0x0DAA3A177EC975CB69BB4ACF4A6E1BE7BCC1AD33D1FFAD97510F9FEA9D8DFF01,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x08)),
            0x19E6822BEB889BE28310060F4FB9741BFD50A31FA81EC65DE21F7B02548D0101,
        )
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
        self.assertEqual(solve(world.current_vm.gas), 863392)

    def test_signextend_BitIsSetInHigherByte(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: signextend_BitIsSetInHigherByte.json
        sha256sum: 52ca3dba40a6c57773094473d20947e065012151d1739b53bdefa3745e5a07c8
        Code:     PUSH3 0x12faf4
                  PUSH1 0x1
                  SIGNEXTEND
                  PUSH1 0x0
                  SSTORE
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
        gaslimit = 10000000
        world = evm.EVMWorld(
            constraints,
            blocknumber=blocknumber,
            timestamp=timestamp,
            difficulty=difficulty,
            coinbase=coinbase,
            gaslimit=gaslimit,
        )

        acc_addr = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        acc_code = unhexlify("6212faf460010b600055")
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F2947DEF4CF144679DA39C4C32BDC35681
        price = 0x5AF3107A4000
        value = 1000000000000000000
        gas = 1000000
        data = ""
        # open a fake tx, no funds send
        world._open_transaction("CALL", address, price, data, caller, value, gas=gas)

        # This variable might seem redundant in some tests - don't forget it is auto generated
        # and there are cases in which we need it ;)
        result, returndata = self._test_run(world)

        # World sanity checks - those should not change, right?
        self.assertEqual(solve(world.block_number()), 0)
        self.assertEqual(solve(world.block_gaslimit()), 10000000)
        self.assertEqual(solve(world.block_timestamp()), 1)
        self.assertEqual(solve(world.block_difficulty()), 256)
        self.assertEqual(solve(world.block_coinbase()), 0x2ADC25665018AA1FE0E6BC666DAC8FC2697FF9BA)

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 0)
        self.assertEqual(
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 1000000000000000000
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6),
            unhexlify("6212faf460010b600055"),
        )
        # check storage
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x00)),
            0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFAF4,
        )
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
        self.assertEqual(solve(world.current_vm.gas), 979986)

    def test_arith1(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: arith1.json
        sha256sum: 89f96edaaf658fa135607f3c623751ad5fc480b5e9817580ca4725c5c523e58f
        Code:     PUSH1 0x1
                  PUSH1 0x1
                  SWAP1
                  ADD
                  PUSH1 0x7
                  MUL
                  PUSH1 0x5
                  ADD
                  PUSH1 0x2
                  SWAP1
                  DIV
                  PUSH1 0x4
                  SWAP1
                  PUSH1 0x1
                  PUSH1 0x21
                  SWAP1
                  SDIV
                  PUSH1 0x15
                  ADD
                  PUSH1 0x3
                  MUL
                  PUSH1 0x5
                  SWAP1
                  SMOD
                  PUSH1 0x3
                  SUB
                  PUSH1 0x9
                  PUSH1 0x11
                  EXP
                  PUSH1 0x0
                  MSTORE
                  PUSH1 0x8
                  PUSH1 0x0
                  RETURN
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
        gaslimit = 10000000
        world = evm.EVMWorld(
            constraints,
            blocknumber=blocknumber,
            timestamp=timestamp,
            difficulty=difficulty,
            coinbase=coinbase,
            gaslimit=gaslimit,
        )

        acc_addr = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        acc_code = unhexlify(
            "6001600190016007026005016002900460049060016021900560150160030260059007600303600960110a60005260086000f3"
        )
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F2947DEF4CF144679DA39C4C32BDC35681
        price = 0x5AF3107A4000
        value = 1000000000000000000
        gas = 1000000
        data = ""
        # open a fake tx, no funds send
        world._open_transaction("CALL", address, price, data, caller, value, gas=gas)

        # This variable might seem redundant in some tests - don't forget it is auto generated
        # and there are cases in which we need it ;)
        result, returndata = self._test_run(world)

        # World sanity checks - those should not change, right?
        self.assertEqual(solve(world.block_number()), 0)
        self.assertEqual(solve(world.block_gaslimit()), 10000000)
        self.assertEqual(solve(world.block_timestamp()), 1)
        self.assertEqual(solve(world.block_difficulty()), 256)
        self.assertEqual(solve(world.block_coinbase()), 0x2ADC25665018AA1FE0E6BC666DAC8FC2697FF9BA)

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 0)
        self.assertEqual(
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 1000000000000000000
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6),
            unhexlify(
                "6001600190016007026005016002900460049060016021900560150160030260059007600303600960110a60005260086000f3"
            ),
        )
        # check outs
        self.assertEqual(returndata, unhexlify("0000000000000000"))
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
        self.assertEqual(solve(world.current_vm.gas), 999871)

    def test_expPowerOf256_33(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: expPowerOf256_33.json
        sha256sum: f2daf3916252f2d92a191ca8ec40e6a6394d64b697e9b1efe88e75200d711db7
        Code:     PUSH1 0x21
                  PUSH2 0x100
                  EXP
                  PUSH1 0x0
                  SSTORE
                  PUSH1 0x21
                  PUSH1 0xff
                  EXP
                  PUSH1 0x1
                  SSTORE
                  PUSH1 0x21
                  PUSH2 0x101
                  EXP
                  PUSH1 0x2
                  SSTORE
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
        acc_code = unhexlify("60216101000a600055602160ff0a60015560216101010a600255")
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F2947DEF4CF144679DA39C4C32BDC35681
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

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 0)
        self.assertEqual(
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 1000000000000000000
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6),
            unhexlify("60216101000a600055602160ff0a60015560216101010a600255"),
        )
        # check storage
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x01)),
            0xFB4C498E11E3F82E714BE514EF024675BB48D678BD192222CD2E783D4DF020FF,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x02)),
            0x25F3884075DD08B8FB400789097AA95DF8750BD17BE0D83C9A0FB7ED52102101,
        )
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
        self.assertEqual(solve(world.current_vm.gas), 54913)

    def test_exp8(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: exp8.json
        sha256sum: 69addad625a0054a7142bc765d5242bb82e834f81a9f4eff97398a1594472990
        Code:     PUSH1 0x0
                  PUSH1 0x0
                  EXP
                  PUSH1 0x0
                  SSTORE
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
        acc_code = unhexlify("600060000a600055")
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F2947DEF4CF144679DA39C4C32BDC35681
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

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 0)
        self.assertEqual(
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 1000000000000000000
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6), unhexlify("600060000a600055")
        )
        # check storage
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x00)), 0x01
        )
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
        self.assertEqual(solve(world.current_vm.gas), 79981)

    def test_mul4(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: mul4.json
        sha256sum: 2af8c375f77e6c86727181d0e3f29f8dbaf405887b13334db8a96f03b44d6f09
        Code:     PUSH32 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
                  PUSH32 0x8000000000000000000000000000000000000000000000000000000000000000
                  MUL
                  PUSH1 0x0
                  SSTORE
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
        acc_code = unhexlify(
            "7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7f800000000000000000000000000000000000000000000000000000000000000002600055"
        )
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F2947DEF4CF144679DA39C4C32BDC35681
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

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 0)
        self.assertEqual(
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 1000000000000000000
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6),
            unhexlify(
                "7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7f800000000000000000000000000000000000000000000000000000000000000002600055"
            ),
        )
        # check storage
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x00)),
            0x8000000000000000000000000000000000000000000000000000000000000000,
        )
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
        self.assertEqual(solve(world.current_vm.gas), 79986)

    def test_sdiv7(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: sdiv7.json
        sha256sum: b097c73bc2c4c5f2329abef383205580973442668673b6fb6feccd151c866c39
        Code:     PUSH1 0x19
                  PUSH1 0x1
                  PUSH1 0x0
                  SUB
                  SDIV
                  PUSH1 0x0
                  SSTORE
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
        acc_code = unhexlify("6019600160000305600055")
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F2947DEF4CF144679DA39C4C32BDC35681
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

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 0)
        self.assertEqual(
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 1000000000000000000
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6),
            unhexlify("6019600160000305600055"),
        )
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
        self.assertEqual(solve(world.current_vm.gas), 94980)

    def test_expPowerOf256Of256_15(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: expPowerOf256Of256_15.json
        sha256sum: 6ba6936af4d67ffb437014aa5d698d8f372d3be932fc1b262b9b9506c36508ac
        Code:     PUSH1 0xf
                  PUSH2 0x100
                  EXP
                  PUSH2 0x100
                  EXP
                  PUSH1 0x0
                  SSTORE
                  PUSH1 0xf
                  PUSH1 0xff
                  EXP
                  PUSH2 0x100
                  EXP
                  PUSH1 0x1
                  SSTORE
                  PUSH1 0xf
                  PUSH2 0x101
                  EXP
                  PUSH2 0x100
                  EXP
                  PUSH1 0x2
                  SSTORE
                  PUSH1 0xf
                  PUSH2 0x100
                  EXP
                  PUSH1 0xff
                  EXP
                  PUSH1 0x3
                  SSTORE
                  PUSH1 0xf
                  PUSH1 0xff
                  EXP
                  PUSH1 0xff
                  EXP
                  PUSH1 0x4
                  SSTORE
                  PUSH1 0xf
                  PUSH2 0x101
                  EXP
                  PUSH1 0xff
                  EXP
                  PUSH1 0x5
                  SSTORE
                  PUSH1 0xf
                  PUSH2 0x100
                  EXP
                  PUSH2 0x101
                  EXP
                  PUSH1 0x6
                  SSTORE
                  PUSH1 0xf
                  PUSH1 0xff
                  EXP
                  PUSH2 0x101
                  EXP
                  PUSH1 0x7
                  SSTORE
                  PUSH1 0xf
                  PUSH2 0x101
                  EXP
                  PUSH2 0x101
                  EXP
                  PUSH1 0x8
                  SSTORE
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
        gaslimit = 10000000
        world = evm.EVMWorld(
            constraints,
            blocknumber=blocknumber,
            timestamp=timestamp,
            difficulty=difficulty,
            coinbase=coinbase,
            gaslimit=gaslimit,
        )

        acc_addr = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        acc_code = unhexlify(
            "600f6101000a6101000a600055600f60ff0a6101000a600155600f6101010a6101000a600255600f6101000a60ff0a600355600f60ff0a60ff0a600455600f6101010a60ff0a600555600f6101000a6101010a600655600f60ff0a6101010a600755600f6101010a6101010a600855"
        )
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F2947DEF4CF144679DA39C4C32BDC35681
        price = 0x5AF3107A4000
        value = 1000000000000000000
        gas = 1000000
        data = ""
        # open a fake tx, no funds send
        world._open_transaction("CALL", address, price, data, caller, value, gas=gas)

        # This variable might seem redundant in some tests - don't forget it is auto generated
        # and there are cases in which we need it ;)
        result, returndata = self._test_run(world)

        # World sanity checks - those should not change, right?
        self.assertEqual(solve(world.block_number()), 0)
        self.assertEqual(solve(world.block_gaslimit()), 10000000)
        self.assertEqual(solve(world.block_timestamp()), 1)
        self.assertEqual(solve(world.block_difficulty()), 256)
        self.assertEqual(solve(world.block_coinbase()), 0x2ADC25665018AA1FE0E6BC666DAC8FC2697FF9BA)

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 0)
        self.assertEqual(
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 1000000000000000000
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6),
            unhexlify(
                "600f6101000a6101000a600055600f60ff0a6101000a600155600f6101010a6101000a600255600f6101000a60ff0a600355600f60ff0a60ff0a600455600f6101010a60ff0a600555600f6101000a6101010a600655600f60ff0a6101010a600755600f6101010a6101010a600855"
            ),
        )
        # check storage
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x03)),
            0x9882EC698218879EC55C33085514FF7F00000000000000000000000000000001,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x04)),
            0x75C4915E18B96704209738F5CA765568BB4DC4113D56683977825A132C8DFEFF,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x05)),
            0x5C76839BF5A80B1DA705DBDF43E4DD6770CD7501AF11FF2DAB7918DFE18F00FF,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x06)),
            0xBF228FC9B0F000B68FB921F7AA6AFF8100000000000000000000000000000001,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x07)),
            0xC6A29131E7594004BC2AA79F0D2C402A1409C57C77D284C14B1A3AB0FF8FFF01,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x08)),
            0xE6B3E5CF6EC90E532FEF7D08455EBF92A03E9E3F6E224EA0FEBDF1A9F08F0101,
        )
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
        self.assertEqual(solve(world.current_vm.gas), 863212)

    def test_divByZero_2(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: divByZero_2.json
        sha256sum: 2d0cd8a2e436a23eae21777e1eed26d4a93c95f3ab2acb277b159d7239b4c36c
        Code:     PUSH1 0x7
                  PUSH1 0x0
                  PUSH1 0xd
                  DIV
                  ADD
                  PUSH1 0x0
                  SSTORE
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
        acc_code = unhexlify("60076000600d0401600055")
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F2947DEF4CF144679DA39C4C32BDC35681
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

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 0)
        self.assertEqual(
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 1000000000000000000
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6),
            unhexlify("60076000600d0401600055"),
        )
        # check storage
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x00)), 0x07
        )
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
        self.assertEqual(solve(world.current_vm.gas), 79980)

    def test_expPowerOf256Of256_26(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: expPowerOf256Of256_26.json
        sha256sum: 9604373efccedf792396c63e83e62c70689d3d7cf3ceba25dd2fdeb37cf8308b
        Code:     PUSH1 0x1a
                  PUSH2 0x100
                  EXP
                  PUSH2 0x100
                  EXP
                  PUSH1 0x0
                  SSTORE
                  PUSH1 0x1a
                  PUSH1 0xff
                  EXP
                  PUSH2 0x100
                  EXP
                  PUSH1 0x1
                  SSTORE
                  PUSH1 0x1a
                  PUSH2 0x101
                  EXP
                  PUSH2 0x100
                  EXP
                  PUSH1 0x2
                  SSTORE
                  PUSH1 0x1a
                  PUSH2 0x100
                  EXP
                  PUSH1 0xff
                  EXP
                  PUSH1 0x3
                  SSTORE
                  PUSH1 0x1a
                  PUSH1 0xff
                  EXP
                  PUSH1 0xff
                  EXP
                  PUSH1 0x4
                  SSTORE
                  PUSH1 0x1a
                  PUSH2 0x101
                  EXP
                  PUSH1 0xff
                  EXP
                  PUSH1 0x5
                  SSTORE
                  PUSH1 0x1a
                  PUSH2 0x100
                  EXP
                  PUSH2 0x101
                  EXP
                  PUSH1 0x6
                  SSTORE
                  PUSH1 0x1a
                  PUSH1 0xff
                  EXP
                  PUSH2 0x101
                  EXP
                  PUSH1 0x7
                  SSTORE
                  PUSH1 0x1a
                  PUSH2 0x101
                  EXP
                  PUSH2 0x101
                  EXP
                  PUSH1 0x8
                  SSTORE
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
        gaslimit = 10000000
        world = evm.EVMWorld(
            constraints,
            blocknumber=blocknumber,
            timestamp=timestamp,
            difficulty=difficulty,
            coinbase=coinbase,
            gaslimit=gaslimit,
        )

        acc_addr = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        acc_code = unhexlify(
            "601a6101000a6101000a600055601a60ff0a6101000a600155601a6101010a6101000a600255601a6101000a60ff0a600355601a60ff0a60ff0a600455601a6101010a60ff0a600555601a6101000a6101010a600655601a60ff0a6101010a600755601a6101010a6101010a600855"
        )
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F2947DEF4CF144679DA39C4C32BDC35681
        price = 0x5AF3107A4000
        value = 1000000000000000000
        gas = 1000000
        data = ""
        # open a fake tx, no funds send
        world._open_transaction("CALL", address, price, data, caller, value, gas=gas)

        # This variable might seem redundant in some tests - don't forget it is auto generated
        # and there are cases in which we need it ;)
        result, returndata = self._test_run(world)

        # World sanity checks - those should not change, right?
        self.assertEqual(solve(world.block_number()), 0)
        self.assertEqual(solve(world.block_gaslimit()), 10000000)
        self.assertEqual(solve(world.block_timestamp()), 1)
        self.assertEqual(solve(world.block_difficulty()), 256)
        self.assertEqual(solve(world.block_coinbase()), 0x2ADC25665018AA1FE0E6BC666DAC8FC2697FF9BA)

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 0)
        self.assertEqual(
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 1000000000000000000
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6),
            unhexlify(
                "601a6101000a6101000a600055601a60ff0a6101000a600155601a6101010a6101000a600255601a6101000a60ff0a600355601a60ff0a60ff0a600455601a6101010a60ff0a600555601a6101000a6101010a600655601a60ff0a6101010a600755601a6101010a6101010a600855"
            ),
        )
        # check storage
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x03)),
            0x085514FF7F000000000000000000000000000000000000000000000000000001,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x04)),
            0x1D164DB738EB6893868B361AD2803F97BE35764456E82A837667A693D1E600FF,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x05)),
            0x8B92C24ABEBF376A5AAB5FF4DFD3538A03D38A10BCED2AAE8E1A8A85B81A00FF,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x06)),
            0xF7AA6AFF81000000000000000000000000000000000000000000000000000001,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x07)),
            0x6931BDA98C70E860A1F6A5224940F1EC7E6734CD9456C95806384F7CB7E60101,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x08)),
            0x3402A9DB66492DFC2A220715E76243469462F24EDC56903BA1D8E96ED21A0101,
        )
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
        self.assertEqual(solve(world.current_vm.gas), 862222)

    def test_addmodDivByZero2(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: addmodDivByZero2.json
        sha256sum: 8ff606d5cf2b15305c314d3aac201a020656517db4b5b8a5730996bf2dc1b161
        Code:     PUSH1 0x0
                  PUSH1 0x0
                  PUSH1 0x1
                  ADDMOD
                  PUSH1 0x0
                  SSTORE
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
        acc_code = unhexlify("60006000600108600055")
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F2947DEF4CF144679DA39C4C32BDC35681
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

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 0)
        self.assertEqual(
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 1000000000000000000
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6),
            unhexlify("60006000600108600055"),
        )
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
        self.assertEqual(solve(world.current_vm.gas), 94980)

    def test_expPowerOf256_29(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: expPowerOf256_29.json
        sha256sum: 7002014dfffb7c97759aab32cc66a6a0017742354d0df30b3189c553ef2a09a3
        Code:     PUSH1 0x1d
                  PUSH2 0x100
                  EXP
                  PUSH1 0x0
                  SSTORE
                  PUSH1 0x1d
                  PUSH1 0xff
                  EXP
                  PUSH1 0x1
                  SSTORE
                  PUSH1 0x1d
                  PUSH2 0x101
                  EXP
                  PUSH1 0x2
                  SSTORE
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
        acc_code = unhexlify("601d6101000a600055601d60ff0a600155601d6101010a600255")
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F2947DEF4CF144679DA39C4C32BDC35681
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

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 0)
        self.assertEqual(
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 1000000000000000000
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6),
            unhexlify("601d6101000a600055601d60ff0a600155601d6101010a600255"),
        )
        # check storage
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x00)),
            0x010000000000000000000000000000000000000000000000000000000000,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x01)),
            0xE48814FE44FC1A8F78642D946D7C879B39A055B6988E438647446A1CFF,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x02)),
            0x011EA4A49E3A9EE435D23F98A8826A875A9AE54CB3090D5C3FD547961D01,
        )
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
        self.assertEqual(solve(world.current_vm.gas), 39913)

    def test_expPowerOf256_1(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: expPowerOf256_1.json
        sha256sum: 584202e492d8a62690f8e65908748e1f05862ead2b1a3e65a02d5598ee1818d5
        Code:     PUSH1 0x1
                  PUSH2 0x100
                  EXP
                  PUSH1 0x0
                  SSTORE
                  PUSH1 0x1
                  PUSH1 0xff
                  EXP
                  PUSH1 0x1
                  SSTORE
                  PUSH1 0x1
                  PUSH2 0x101
                  EXP
                  PUSH1 0x2
                  SSTORE
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
        acc_code = unhexlify("60016101000a600055600160ff0a60015560016101010a600255")
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F2947DEF4CF144679DA39C4C32BDC35681
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

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 0)
        self.assertEqual(
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 1000000000000000000
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6),
            unhexlify("60016101000a600055600160ff0a60015560016101010a600255"),
        )
        # check storage
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x00)), 0x0100
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x01)), 0xFF
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x02)), 0x0101
        )
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
        self.assertEqual(solve(world.current_vm.gas), 39913)

    def test_signextend_BigByteBigByte(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: signextend_BigByteBigByte.json
        sha256sum: 75518a6c534f0b47b7217ca634c45f8deec9c202c789d0055e91769e3d59527c
        Code:     PUSH32 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
                  PUSH32 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
                  SIGNEXTEND
                  PUSH1 0x0
                  SSTORE
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
        gaslimit = 10000000
        world = evm.EVMWorld(
            constraints,
            blocknumber=blocknumber,
            timestamp=timestamp,
            difficulty=difficulty,
            coinbase=coinbase,
            gaslimit=gaslimit,
        )

        acc_addr = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        acc_code = unhexlify(
            "7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0b600055"
        )
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F2947DEF4CF144679DA39C4C32BDC35681
        price = 0x5AF3107A4000
        value = 1000000000000000000
        gas = 1000000
        data = ""
        # open a fake tx, no funds send
        world._open_transaction("CALL", address, price, data, caller, value, gas=gas)

        # This variable might seem redundant in some tests - don't forget it is auto generated
        # and there are cases in which we need it ;)
        result, returndata = self._test_run(world)

        # World sanity checks - those should not change, right?
        self.assertEqual(solve(world.block_number()), 0)
        self.assertEqual(solve(world.block_gaslimit()), 10000000)
        self.assertEqual(solve(world.block_timestamp()), 1)
        self.assertEqual(solve(world.block_difficulty()), 256)
        self.assertEqual(solve(world.block_coinbase()), 0x2ADC25665018AA1FE0E6BC666DAC8FC2697FF9BA)

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 0)
        self.assertEqual(
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 1000000000000000000
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6),
            unhexlify(
                "7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0b600055"
            ),
        )
        # check storage
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x00)),
            0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF,
        )
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
        self.assertEqual(solve(world.current_vm.gas), 979986)

    def test_expPowerOf256_4(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: expPowerOf256_4.json
        sha256sum: 2c69a6e43ce8c44ae607fd6eb3b2fc3bda3955f616443834561d2591e66a2b5c
        Code:     PUSH1 0x4
                  PUSH2 0x100
                  EXP
                  PUSH1 0x0
                  SSTORE
                  PUSH1 0x4
                  PUSH1 0xff
                  EXP
                  PUSH1 0x1
                  SSTORE
                  PUSH1 0x4
                  PUSH2 0x101
                  EXP
                  PUSH1 0x2
                  SSTORE
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
        acc_code = unhexlify("60046101000a600055600460ff0a60015560046101010a600255")
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F2947DEF4CF144679DA39C4C32BDC35681
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

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 0)
        self.assertEqual(
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 1000000000000000000
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6),
            unhexlify("60046101000a600055600460ff0a60015560046101010a600255"),
        )
        # check storage
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x00)),
            0x0100000000,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x01)),
            0xFC05FC01,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x02)),
            0x0104060401,
        )
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
        self.assertEqual(solve(world.current_vm.gas), 39913)

    def test_signextend_BitIsNotSetInHigherByte(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: signextend_BitIsNotSetInHigherByte.json
        sha256sum: a84b4f3be5bb727c6040dde6c8fcdf0267e1b1db6005ecc8234acca9e7868b5a
        Code:     PUSH3 0x126af4
                  PUSH1 0x1
                  SIGNEXTEND
                  PUSH1 0x0
                  SSTORE
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
        gaslimit = 10000000
        world = evm.EVMWorld(
            constraints,
            blocknumber=blocknumber,
            timestamp=timestamp,
            difficulty=difficulty,
            coinbase=coinbase,
            gaslimit=gaslimit,
        )

        acc_addr = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        acc_code = unhexlify("62126af460010b600055")
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F2947DEF4CF144679DA39C4C32BDC35681
        price = 0x5AF3107A4000
        value = 1000000000000000000
        gas = 1000000
        data = ""
        # open a fake tx, no funds send
        world._open_transaction("CALL", address, price, data, caller, value, gas=gas)

        # This variable might seem redundant in some tests - don't forget it is auto generated
        # and there are cases in which we need it ;)
        result, returndata = self._test_run(world)

        # World sanity checks - those should not change, right?
        self.assertEqual(solve(world.block_number()), 0)
        self.assertEqual(solve(world.block_gaslimit()), 10000000)
        self.assertEqual(solve(world.block_timestamp()), 1)
        self.assertEqual(solve(world.block_difficulty()), 256)
        self.assertEqual(solve(world.block_coinbase()), 0x2ADC25665018AA1FE0E6BC666DAC8FC2697FF9BA)

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 0)
        self.assertEqual(
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 1000000000000000000
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6),
            unhexlify("62126af460010b600055"),
        )
        # check storage
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x00)), 0x6AF4
        )
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
        self.assertEqual(solve(world.current_vm.gas), 979986)

    def test_signextend_BigByte_0(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: signextend_BigByte_0.json
        sha256sum: 55f9f4e253517d1ac56053c4e71c32eb1b18d40d5ea754683851ea356ae9daa1
        Code:     PUSH1 0x0
                  PUSH32 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
                  SIGNEXTEND
                  PUSH1 0x0
                  SSTORE
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
        gaslimit = 10000000
        world = evm.EVMWorld(
            constraints,
            blocknumber=blocknumber,
            timestamp=timestamp,
            difficulty=difficulty,
            coinbase=coinbase,
            gaslimit=gaslimit,
        )

        acc_addr = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        acc_code = unhexlify(
            "60007fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0b600055"
        )
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F2947DEF4CF144679DA39C4C32BDC35681
        price = 0x5AF3107A4000
        value = 1000000000000000000
        gas = 1000000
        data = ""
        # open a fake tx, no funds send
        world._open_transaction("CALL", address, price, data, caller, value, gas=gas)

        # This variable might seem redundant in some tests - don't forget it is auto generated
        # and there are cases in which we need it ;)
        result, returndata = self._test_run(world)

        # World sanity checks - those should not change, right?
        self.assertEqual(solve(world.block_number()), 0)
        self.assertEqual(solve(world.block_gaslimit()), 10000000)
        self.assertEqual(solve(world.block_timestamp()), 1)
        self.assertEqual(solve(world.block_difficulty()), 256)
        self.assertEqual(solve(world.block_coinbase()), 0x2ADC25665018AA1FE0E6BC666DAC8FC2697FF9BA)

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 0)
        self.assertEqual(
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 1000000000000000000
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6),
            unhexlify(
                "60007fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0b600055"
            ),
        )
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
        self.assertEqual(solve(world.current_vm.gas), 994986)

    def test_signextend_bitIsSet(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: signextend_bitIsSet.json
        sha256sum: c763feca37e8b16e1187232879fc3fc7fad7c4c5b0c22e2098bfc90fc708a2b4
        Code:     PUSH3 0x122ff4
                  PUSH1 0x0
                  SIGNEXTEND
                  PUSH1 0x0
                  SSTORE
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
        gaslimit = 10000000
        world = evm.EVMWorld(
            constraints,
            blocknumber=blocknumber,
            timestamp=timestamp,
            difficulty=difficulty,
            coinbase=coinbase,
            gaslimit=gaslimit,
        )

        acc_addr = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        acc_code = unhexlify("62122ff460000b600055")
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F2947DEF4CF144679DA39C4C32BDC35681
        price = 0x5AF3107A4000
        value = 1000000000000000000
        gas = 1000000
        data = ""
        # open a fake tx, no funds send
        world._open_transaction("CALL", address, price, data, caller, value, gas=gas)

        # This variable might seem redundant in some tests - don't forget it is auto generated
        # and there are cases in which we need it ;)
        result, returndata = self._test_run(world)

        # World sanity checks - those should not change, right?
        self.assertEqual(solve(world.block_number()), 0)
        self.assertEqual(solve(world.block_gaslimit()), 10000000)
        self.assertEqual(solve(world.block_timestamp()), 1)
        self.assertEqual(solve(world.block_difficulty()), 256)
        self.assertEqual(solve(world.block_coinbase()), 0x2ADC25665018AA1FE0E6BC666DAC8FC2697FF9BA)

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 0)
        self.assertEqual(
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 1000000000000000000
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6),
            unhexlify("62122ff460000b600055"),
        )
        # check storage
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x00)),
            0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF4,
        )
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
        self.assertEqual(solve(world.current_vm.gas), 979986)

    def test_mod0(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: mod0.json
        sha256sum: c637f138f8fbd9296d552b44d2b5a2fcd30586689eb2310765ca0fb78ee0ebf4
        Code:     PUSH1 0x3
                  PUSH1 0x2
                  MOD
                  PUSH1 0x0
                  SSTORE
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
        acc_code = unhexlify("6003600206600055")
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F2947DEF4CF144679DA39C4C32BDC35681
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

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 0)
        self.assertEqual(
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 1000000000000000000
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6), unhexlify("6003600206600055")
        )
        # check storage
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x00)), 0x02
        )
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
        self.assertEqual(solve(world.current_vm.gas), 79986)

    def test_sub4(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: sub4.json
        sha256sum: 7aa553398de51c541b626d1f247ca57e6fe0037f64ef1e25f8811eabd8c32333
        Code:     PUSH1 0x0
                  PUSH32 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
                  SUB
                  PUSH1 0x0
                  SSTORE
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
        acc_code = unhexlify(
            "60007fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff03600055"
        )
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F2947DEF4CF144679DA39C4C32BDC35681
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

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 0)
        self.assertEqual(
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 1000000000000000000
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6),
            unhexlify(
                "60007fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff03600055"
            ),
        )
        # check storage
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x00)),
            0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF,
        )
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
        self.assertEqual(solve(world.current_vm.gas), 79988)

    def test_smod_i256min2(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: smod_i256min2.json
        sha256sum: e4e1b0c5b6cb075722450891a8021b351ef372c6cd0ac462eabe87f7527f8ac6
        Code:     PUSH1 0x1
                  PUSH1 0x1
                  PUSH1 0x0
                  SUB
                  PUSH32 0x8000000000000000000000000000000000000000000000000000000000000000
                  PUSH1 0x0
                  SUB
                  SMOD
                  SUB
                  PUSH1 0x0
                  SSTORE
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
        acc_code = unhexlify(
            "600160016000037f80000000000000000000000000000000000000000000000000000000000000006000030703600055"
        )
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F2947DEF4CF144679DA39C4C32BDC35681
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

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 0)
        self.assertEqual(
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 1000000000000000000
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6),
            unhexlify(
                "600160016000037f80000000000000000000000000000000000000000000000000000000000000006000030703600055"
            ),
        )
        # check storage
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x00)),
            0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF,
        )
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
        self.assertEqual(solve(world.current_vm.gas), 79968)

    def test_exp0(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: exp0.json
        sha256sum: 208b278b3eb8274133ca427c82a0ff718fdcfe1871b1b4c0fb9fa3c573b260f4
        Code:     PUSH1 0x2
                  PUSH1 0x2
                  EXP
                  PUSH1 0x0
                  SSTORE
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
        acc_code = unhexlify("600260020a600055")
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F2947DEF4CF144679DA39C4C32BDC35681
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

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 0)
        self.assertEqual(
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 1000000000000000000
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6), unhexlify("600260020a600055")
        )
        # check storage
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x00)), 0x04
        )
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
        self.assertEqual(solve(world.current_vm.gas), 79971)

    def test_expPowerOf256Of256_30(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: expPowerOf256Of256_30.json
        sha256sum: 9be1de88639c668f65e96e5d6a8580acd53611be901cdbfdd45a967d85ff4b47
        Code:     PUSH1 0x1e
                  PUSH2 0x100
                  EXP
                  PUSH2 0x100
                  EXP
                  PUSH1 0x0
                  SSTORE
                  PUSH1 0x1e
                  PUSH1 0xff
                  EXP
                  PUSH2 0x100
                  EXP
                  PUSH1 0x1
                  SSTORE
                  PUSH1 0x1e
                  PUSH2 0x101
                  EXP
                  PUSH2 0x100
                  EXP
                  PUSH1 0x2
                  SSTORE
                  PUSH1 0x1e
                  PUSH2 0x100
                  EXP
                  PUSH1 0xff
                  EXP
                  PUSH1 0x3
                  SSTORE
                  PUSH1 0x1e
                  PUSH1 0xff
                  EXP
                  PUSH1 0xff
                  EXP
                  PUSH1 0x4
                  SSTORE
                  PUSH1 0x1e
                  PUSH2 0x101
                  EXP
                  PUSH1 0xff
                  EXP
                  PUSH1 0x5
                  SSTORE
                  PUSH1 0x1e
                  PUSH2 0x100
                  EXP
                  PUSH2 0x101
                  EXP
                  PUSH1 0x6
                  SSTORE
                  PUSH1 0x1e
                  PUSH1 0xff
                  EXP
                  PUSH2 0x101
                  EXP
                  PUSH1 0x7
                  SSTORE
                  PUSH1 0x1e
                  PUSH2 0x101
                  EXP
                  PUSH2 0x101
                  EXP
                  PUSH1 0x8
                  SSTORE
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
        gaslimit = 10000000
        world = evm.EVMWorld(
            constraints,
            blocknumber=blocknumber,
            timestamp=timestamp,
            difficulty=difficulty,
            coinbase=coinbase,
            gaslimit=gaslimit,
        )

        acc_addr = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        acc_code = unhexlify(
            "601e6101000a6101000a600055601e60ff0a6101000a600155601e6101010a6101000a600255601e6101000a60ff0a600355601e60ff0a60ff0a600455601e6101010a60ff0a600555601e6101000a6101010a600655601e60ff0a6101010a600755601e6101010a6101010a600855"
        )
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F2947DEF4CF144679DA39C4C32BDC35681
        price = 0x5AF3107A4000
        value = 1000000000000000000
        gas = 1000000
        data = ""
        # open a fake tx, no funds send
        world._open_transaction("CALL", address, price, data, caller, value, gas=gas)

        # This variable might seem redundant in some tests - don't forget it is auto generated
        # and there are cases in which we need it ;)
        result, returndata = self._test_run(world)

        # World sanity checks - those should not change, right?
        self.assertEqual(solve(world.block_number()), 0)
        self.assertEqual(solve(world.block_gaslimit()), 10000000)
        self.assertEqual(solve(world.block_timestamp()), 1)
        self.assertEqual(solve(world.block_difficulty()), 256)
        self.assertEqual(solve(world.block_coinbase()), 0x2ADC25665018AA1FE0E6BC666DAC8FC2697FF9BA)

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 0)
        self.assertEqual(
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 1000000000000000000
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6),
            unhexlify(
                "601e6101000a6101000a600055601e60ff0a6101000a600155601e6101010a6101000a600255601e6101000a60ff0a600355601e60ff0a60ff0a600455601e6101010a60ff0a600555601e6101000a6101010a600655601e60ff0a6101010a600755601e6101010a6101010a600855"
            ),
        )
        # check storage
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x03)),
            0x7F00000000000000000000000000000000000000000000000000000000000001,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x04)),
            0xE9772778F50FA0A69CD10FA019AC56D72AC7A7D7AF26C4BA28415C8F41E200FF,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x05)),
            0x33F0385EF73FEEBDB952E5ADB643DD0FA178FD9271578219AD50A73D241E00FF,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x06)),
            0x8100000000000000000000000000000000000000000000000000000000000001,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x07)),
            0xFD405CCE8F73DFFC04A6F0FF6FFC6BF7961876D09C5B4933A68F0CC623E20101,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x08)),
            0xC5A8F4566FD2E96E4CE3A8B3EC0863E7B20BC3B2F3DC5261BA8A0174421E0101,
        )
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
        self.assertEqual(solve(world.current_vm.gas), 861862)

    def test_mulmod1_overflow3(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: mulmod1_overflow3.json
        sha256sum: e626164ad7fe44a9b5d88a3f65b2abb79843fb4e497c9f38f617045575d83a21
        Code:     PUSH1 0x5
                  PUSH1 0x2
                  PUSH32 0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
                  MULMOD
                  PUSH1 0x0
                  SSTORE
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
        acc_code = unhexlify(
            "600560027f7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff09600055"
        )
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F2947DEF4CF144679DA39C4C32BDC35681
        price = 0x5AF3107A4000
        value = 1000000000000000000
        gas = 1000000
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

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 0)
        self.assertEqual(
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 1000000000000000000
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6),
            unhexlify(
                "600560027f7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff09600055"
            ),
        )
        # check storage
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x00)), 0x04
        )
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
        self.assertEqual(solve(world.current_vm.gas), 979980)

    def test_expPowerOf256Of256_2(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: expPowerOf256Of256_2.json
        sha256sum: cde732ffd8858cd61f0586632164327d840f78943df0821504ca9be92766d243
        Code:     PUSH1 0x2
                  PUSH2 0x100
                  EXP
                  PUSH2 0x100
                  EXP
                  PUSH1 0x0
                  SSTORE
                  PUSH1 0x2
                  PUSH1 0xff
                  EXP
                  PUSH2 0x100
                  EXP
                  PUSH1 0x1
                  SSTORE
                  PUSH1 0x2
                  PUSH2 0x101
                  EXP
                  PUSH2 0x100
                  EXP
                  PUSH1 0x2
                  SSTORE
                  PUSH1 0x2
                  PUSH2 0x100
                  EXP
                  PUSH1 0xff
                  EXP
                  PUSH1 0x3
                  SSTORE
                  PUSH1 0x2
                  PUSH1 0xff
                  EXP
                  PUSH1 0xff
                  EXP
                  PUSH1 0x4
                  SSTORE
                  PUSH1 0x2
                  PUSH2 0x101
                  EXP
                  PUSH1 0xff
                  EXP
                  PUSH1 0x5
                  SSTORE
                  PUSH1 0x2
                  PUSH2 0x100
                  EXP
                  PUSH2 0x101
                  EXP
                  PUSH1 0x6
                  SSTORE
                  PUSH1 0x2
                  PUSH1 0xff
                  EXP
                  PUSH2 0x101
                  EXP
                  PUSH1 0x7
                  SSTORE
                  PUSH1 0x2
                  PUSH2 0x101
                  EXP
                  PUSH2 0x101
                  EXP
                  PUSH1 0x8
                  SSTORE
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
        gaslimit = 10000000
        world = evm.EVMWorld(
            constraints,
            blocknumber=blocknumber,
            timestamp=timestamp,
            difficulty=difficulty,
            coinbase=coinbase,
            gaslimit=gaslimit,
        )

        acc_addr = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        acc_code = unhexlify(
            "60026101000a6101000a600055600260ff0a6101000a60015560026101010a6101000a60025560026101000a60ff0a600355600260ff0a60ff0a60045560026101010a60ff0a60055560026101000a6101010a600655600260ff0a6101010a60075560026101010a6101010a600855"
        )
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F2947DEF4CF144679DA39C4C32BDC35681
        price = 0x5AF3107A4000
        value = 1000000000000000000
        gas = 1000000
        data = ""
        # open a fake tx, no funds send
        world._open_transaction("CALL", address, price, data, caller, value, gas=gas)

        # This variable might seem redundant in some tests - don't forget it is auto generated
        # and there are cases in which we need it ;)
        result, returndata = self._test_run(world)

        # World sanity checks - those should not change, right?
        self.assertEqual(solve(world.block_number()), 0)
        self.assertEqual(solve(world.block_gaslimit()), 10000000)
        self.assertEqual(solve(world.block_timestamp()), 1)
        self.assertEqual(solve(world.block_difficulty()), 256)
        self.assertEqual(solve(world.block_coinbase()), 0x2ADC25665018AA1FE0E6BC666DAC8FC2697FF9BA)

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 0)
        self.assertEqual(
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 1000000000000000000
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6),
            unhexlify(
                "60026101000a6101000a600055600260ff0a6101000a60015560026101010a6101000a60025560026101000a60ff0a600355600260ff0a60ff0a60045560026101010a60ff0a60055560026101000a6101010a600655600260ff0a6101010a60075560026101010a6101010a600855"
            ),
        )
        # check storage
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x03)),
            0x4EE4CEEAAC565C81F55A87C43F82F7C889EF4FC7C679671E28D594FF7F000001,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x04)),
            0x82F46A1B4E34D66712910615D2571D75606CEAC51FA8CA8C58CF6CA881FE00FF,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x05)),
            0x81C9FCEFA5DE158AE2007F25D35C0D11CD735342A48905955A5A6852800200FF,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x06)),
            0x666AC362902470ED850709E2A29969D10CBA09DEBC03C38D172AEAFF81000001,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x07)),
            0xEB30A3C678A01BDE914548F98F3366DC0FFE9F85384EBF1111D03DAD7FFE0101,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x08)),
            0x72D0A7939B6303CE1D46E6E3F1B8BE303BFDB2B00F41AD8076B0975782020101,
        )
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
        self.assertEqual(solve(world.current_vm.gas), 864382)

    def test_sdiv6(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: sdiv6.json
        sha256sum: 391a875666f18ddd1d4bfedc31e6460f696d40698ff1ddeb6b52f9454cff0ba7
        Code:     PUSH1 0x0
                  PUSH32 0x8000000000000000000000000000000000000000000000000000000000000000
                  PUSH1 0x0
                  SUB
                  SDIV
                  PUSH1 0x0
                  SSTORE
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
        acc_code = unhexlify(
            "60007f800000000000000000000000000000000000000000000000000000000000000060000305600055"
        )
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F2947DEF4CF144679DA39C4C32BDC35681
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

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 0)
        self.assertEqual(
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 1000000000000000000
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6),
            unhexlify(
                "60007f800000000000000000000000000000000000000000000000000000000000000060000305600055"
            ),
        )
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
        self.assertEqual(solve(world.current_vm.gas), 94980)

    def test_mulmod2_1(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: mulmod2_1.json
        sha256sum: 0c688ca9972d5d25c4dfe4fbc99c6b6796773acbdf9076afa799682c3e60ca7e
        Code:     PUSH1 0x3
                  PUSH1 0x1
                  PUSH1 0x5
                  PUSH1 0x0
                  SUB
                  MULMOD
                  PUSH1 0x3
                  PUSH1 0x5
                  PUSH1 0x0
                  SUB
                  MOD
                  EQ
                  PUSH1 0x0
                  SSTORE
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
        acc_code = unhexlify("60036001600560000309600360056000030614600055")
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F2947DEF4CF144679DA39C4C32BDC35681
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

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 0)
        self.assertEqual(
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 1000000000000000000
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6),
            unhexlify("60036001600560000309600360056000030614600055"),
        )
        # check storage
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x00)), 0x01
        )
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
        self.assertEqual(solve(world.current_vm.gas), 79954)

    def test_sdiv8(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: sdiv8.json
        sha256sum: ae920601baa46dd4e819c59770df6a4df3283f34525ca348cfbefed8fedf2b83
        Code:     PUSH1 0x1
                  PUSH1 0x0
                  SUB
                  PUSH1 0x1
                  PUSH1 0x0
                  SUB
                  SDIV
                  PUSH1 0x0
                  SSTORE
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
        acc_code = unhexlify("6001600003600160000305600055")
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F2947DEF4CF144679DA39C4C32BDC35681
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

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 0)
        self.assertEqual(
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 1000000000000000000
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6),
            unhexlify("6001600003600160000305600055"),
        )
        # check storage
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x00)), 0x01
        )
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
        self.assertEqual(solve(world.current_vm.gas), 79974)

    def test_mod1(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: mod1.json
        sha256sum: 0c9879f653ca8b0f03f685c849ecbf73657d8b7b40a1053950e30d99a05bf692
        Code:     PUSH1 0x2
                  PUSH32 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
                  MOD
                  PUSH1 0x0
                  SSTORE
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
        acc_code = unhexlify(
            "60027fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff06600055"
        )
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F2947DEF4CF144679DA39C4C32BDC35681
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

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 0)
        self.assertEqual(
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 1000000000000000000
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6),
            unhexlify(
                "60027fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff06600055"
            ),
        )
        # check storage
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x00)), 0x01
        )
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
        self.assertEqual(solve(world.current_vm.gas), 79986)

    def test_addmodDivByZero(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: addmodDivByZero.json
        sha256sum: 699b519167c3ca59bb214bb1cad9eacd4e3a3c0ccc9120da44602be1b67c251c
        Code:     PUSH1 0x0
                  PUSH1 0x1
                  PUSH1 0x4
                  ADDMOD
                  PUSH1 0x0
                  SSTORE
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
        acc_code = unhexlify("60006001600408600055")
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F2947DEF4CF144679DA39C4C32BDC35681
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

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 0)
        self.assertEqual(
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 1000000000000000000
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6),
            unhexlify("60006001600408600055"),
        )
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
        self.assertEqual(solve(world.current_vm.gas), 94980)

    def test_mul7(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: mul7.json
        sha256sum: eeb40b21e741cfbc21521e111beb281c4dafff4cbaaa14d53487bb9f0d8518dc
        Code:     PUSH17 0x1234567890abcdef0fedcba0987654321
                  PUSH17 0x1234567890abcdef0fedcba0987654321
                  PUSH17 0x1234567890abcdef0fedcba0987654321
                  MUL
                  MUL
                  PUSH1 0x0
                  MSTORE
                  PUSH1 0x20
                  PUSH1 0x0
                  RETURN
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
        acc_code = unhexlify(
            "7001234567890abcdef0fedcba09876543217001234567890abcdef0fedcba09876543217001234567890abcdef0fedcba0987654321020260005260206000f3"
        )
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F2947DEF4CF144679DA39C4C32BDC35681
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

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 0)
        self.assertEqual(
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 1000000000000000000
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6),
            unhexlify(
                "7001234567890abcdef0fedcba09876543217001234567890abcdef0fedcba09876543217001234567890abcdef0fedcba0987654321020260005260206000f3"
            ),
        )
        # check outs
        self.assertEqual(
            returndata,
            unhexlify("47d0817e4167b1eb4f9fc722b133ef9d7d9a6fb4c2c1c442d000107a5e419561"),
        )
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
        self.assertEqual(solve(world.current_vm.gas), 99966)

    def test_expPowerOf256Of256_22(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: expPowerOf256Of256_22.json
        sha256sum: 66b554633cb22c3619a5b10ea3e4a509c37a667e4d83656c59aaf25dd2f36871
        Code:     PUSH1 0x16
                  PUSH2 0x100
                  EXP
                  PUSH2 0x100
                  EXP
                  PUSH1 0x0
                  SSTORE
                  PUSH1 0x16
                  PUSH1 0xff
                  EXP
                  PUSH2 0x100
                  EXP
                  PUSH1 0x1
                  SSTORE
                  PUSH1 0x16
                  PUSH2 0x101
                  EXP
                  PUSH2 0x100
                  EXP
                  PUSH1 0x2
                  SSTORE
                  PUSH1 0x16
                  PUSH2 0x100
                  EXP
                  PUSH1 0xff
                  EXP
                  PUSH1 0x3
                  SSTORE
                  PUSH1 0x16
                  PUSH1 0xff
                  EXP
                  PUSH1 0xff
                  EXP
                  PUSH1 0x4
                  SSTORE
                  PUSH1 0x16
                  PUSH2 0x101
                  EXP
                  PUSH1 0xff
                  EXP
                  PUSH1 0x5
                  SSTORE
                  PUSH1 0x16
                  PUSH2 0x100
                  EXP
                  PUSH2 0x101
                  EXP
                  PUSH1 0x6
                  SSTORE
                  PUSH1 0x16
                  PUSH1 0xff
                  EXP
                  PUSH2 0x101
                  EXP
                  PUSH1 0x7
                  SSTORE
                  PUSH1 0x16
                  PUSH2 0x101
                  EXP
                  PUSH2 0x101
                  EXP
                  PUSH1 0x8
                  SSTORE
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
        gaslimit = 10000000
        world = evm.EVMWorld(
            constraints,
            blocknumber=blocknumber,
            timestamp=timestamp,
            difficulty=difficulty,
            coinbase=coinbase,
            gaslimit=gaslimit,
        )

        acc_addr = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        acc_code = unhexlify(
            "60166101000a6101000a600055601660ff0a6101000a60015560166101010a6101000a60025560166101000a60ff0a600355601660ff0a60ff0a60045560166101010a60ff0a60055560166101000a6101010a600655601660ff0a6101010a60075560166101010a6101010a600855"
        )
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F2947DEF4CF144679DA39C4C32BDC35681
        price = 0x5AF3107A4000
        value = 1000000000000000000
        gas = 1000000
        data = ""
        # open a fake tx, no funds send
        world._open_transaction("CALL", address, price, data, caller, value, gas=gas)

        # This variable might seem redundant in some tests - don't forget it is auto generated
        # and there are cases in which we need it ;)
        result, returndata = self._test_run(world)

        # World sanity checks - those should not change, right?
        self.assertEqual(solve(world.block_number()), 0)
        self.assertEqual(solve(world.block_gaslimit()), 10000000)
        self.assertEqual(solve(world.block_timestamp()), 1)
        self.assertEqual(solve(world.block_difficulty()), 256)
        self.assertEqual(solve(world.block_coinbase()), 0x2ADC25665018AA1FE0E6BC666DAC8FC2697FF9BA)

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 0)
        self.assertEqual(
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 1000000000000000000
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6),
            unhexlify(
                "60166101000a6101000a600055601660ff0a6101000a60015560166101010a6101000a60025560166101000a60ff0a600355601660ff0a60ff0a60045560166101010a60ff0a60055560166101000a6101010a600655601660ff0a6101010a60075560166101010a6101010a600855"
            ),
        )
        # check storage
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x03)),
            0x9EC55C33085514FF7F0000000000000000000000000000000000000000000001,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x04)),
            0xEC447E662AC08957D7E290A421DBF54C0AAF43AADC9CC465AD0B02F071EA00FF,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x05)),
            0xDC9178D3BAB470096F01477C859B5F4173986640B659426412A653465C1600FF,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x06)),
            0xB68FB921F7AA6AFF810000000000000000000000000000000000000000000001,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x07)),
            0xDCF0A770777610503596AE0311AF46C171151ED45107D7E7BB8F74BB5BEA0101,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x08)),
            0x4D65773387993928C95C861274232D3FB6F6B7FE1B22E4E61A30E71172160101,
        )
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
        self.assertEqual(solve(world.current_vm.gas), 862582)

    def test_sdiv4(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: sdiv4.json
        sha256sum: 064bc920d09d94839707b16d921da2a963ae7f8d6730a48eb8d93c5baee0f7af
        Code:     PUSH1 0x4
                  PUSH1 0x0
                  SUB
                  PUSH1 0x5
                  SDIV
                  PUSH1 0x0
                  SSTORE
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
        acc_code = unhexlify("6004600003600505600055")
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F2947DEF4CF144679DA39C4C32BDC35681
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

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 0)
        self.assertEqual(
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 1000000000000000000
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6),
            unhexlify("6004600003600505600055"),
        )
        # check storage
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x00)),
            0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF,
        )
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
        self.assertEqual(solve(world.current_vm.gas), 79980)

    def test_sdiv2(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: sdiv2.json
        sha256sum: 0f21f478a11e9ec5352a0f83ef56df1d8b0115a04da8b5db731e504165d4c83e
        Code:     PUSH1 0x4
                  PUSH1 0x0
                  SUB
                  PUSH1 0x2
                  PUSH1 0x0
                  SUB
                  SDIV
                  PUSH1 0x0
                  SSTORE
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
        acc_code = unhexlify("6004600003600260000305600055")
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F2947DEF4CF144679DA39C4C32BDC35681
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

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 0)
        self.assertEqual(
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 1000000000000000000
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6),
            unhexlify("6004600003600260000305600055"),
        )
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
        self.assertEqual(solve(world.current_vm.gas), 94974)

    def test_mulmoddivByZero(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: mulmoddivByZero.json
        sha256sum: 70d6b833c9c91d9a01e43a01b248a4a5a63d2e333a73122ab602d690de9cc34a
        Code:     PUSH1 0x0
                  PUSH1 0x1
                  PUSH1 0x5
                  MULMOD
                  PUSH1 0x0
                  SSTORE
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
        acc_code = unhexlify("60006001600509600055")
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F2947DEF4CF144679DA39C4C32BDC35681
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

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 0)
        self.assertEqual(
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 1000000000000000000
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6),
            unhexlify("60006001600509600055"),
        )
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
        self.assertEqual(solve(world.current_vm.gas), 94980)

    def test_smod0(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: smod0.json
        sha256sum: ff6e79c3ee961d27ad631ec3234dbe27f60d5b9cd7a7680387dea3e297f0f3a0
        Code:     PUSH1 0x3
                  PUSH1 0x0
                  SUB
                  PUSH1 0x5
                  PUSH1 0x0
                  SUB
                  SMOD
                  PUSH1 0x0
                  SSTORE
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
        acc_code = unhexlify("6003600003600560000307600055")
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F2947DEF4CF144679DA39C4C32BDC35681
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

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 0)
        self.assertEqual(
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 1000000000000000000
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6),
            unhexlify("6003600003600560000307600055"),
        )
        # check storage
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x00)),
            0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFE,
        )
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
        self.assertEqual(solve(world.current_vm.gas), 79974)

    def test_add2(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: add2.json
        sha256sum: 96dfcc5838c3676c7fefeb38d582b5ef7a5af3fe6303d976f0846542ea124657
        Code:     PUSH1 0x1
                  PUSH32 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
                  ADD
                  PUSH1 0x0
                  SSTORE
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
        acc_code = unhexlify(
            "60017fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff01600055"
        )
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F2947DEF4CF144679DA39C4C32BDC35681
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

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 0)
        self.assertEqual(
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 1000000000000000000
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6),
            unhexlify(
                "60017fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff01600055"
            ),
        )
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
        self.assertEqual(solve(world.current_vm.gas), 94988)

    def test_addmod2_1(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: addmod2_1.json
        sha256sum: 85890ed9d2bbf0ab3c30f1acb13082ee432641d94595b6c975097bb3a72fc840
        Code:     PUSH1 0x3
                  PUSH1 0x1
                  PUSH1 0x6
                  PUSH1 0x0
                  SUB
                  ADDMOD
                  PUSH1 0x3
                  PUSH1 0x5
                  PUSH1 0x0
                  SUB
                  MOD
                  EQ
                  PUSH1 0x0
                  SSTORE
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
        acc_code = unhexlify("60036001600660000308600360056000030614600055")
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F2947DEF4CF144679DA39C4C32BDC35681
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

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 0)
        self.assertEqual(
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 1000000000000000000
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6),
            unhexlify("60036001600660000308600360056000030614600055"),
        )
        # check storage
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x00)), 0x01
        )
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
        self.assertEqual(solve(world.current_vm.gas), 79954)

    def test_expPowerOf256_11(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: expPowerOf256_11.json
        sha256sum: b432ae35edb4ed128ccf71ccae2f9d8bb48d011eb7daa694bcc3f5f22de68593
        Code:     PUSH1 0xb
                  PUSH2 0x100
                  EXP
                  PUSH1 0x0
                  SSTORE
                  PUSH1 0xb
                  PUSH1 0xff
                  EXP
                  PUSH1 0x1
                  SSTORE
                  PUSH1 0xb
                  PUSH2 0x101
                  EXP
                  PUSH1 0x2
                  SSTORE
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
        acc_code = unhexlify("600b6101000a600055600b60ff0a600155600b6101010a600255")
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F2947DEF4CF144679DA39C4C32BDC35681
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

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 0)
        self.assertEqual(
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 1000000000000000000
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6),
            unhexlify("600b6101000a600055600b60ff0a600155600b6101010a600255"),
        )
        # check storage
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x00)),
            0x010000000000000000000000,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x01)),
            0xF5365C4833CCB6A4C90AFF,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x02)),
            0x010B37A64BCFCF4AA5370B01,
        )
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
        self.assertEqual(solve(world.current_vm.gas), 39913)

    def test_expPowerOf256Of256_28(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: expPowerOf256Of256_28.json
        sha256sum: 2f1ae9d4d2a53e46e60c0bbc00f15360912d71e1fed2fd41f9e6839dbffdb05e
        Code:     PUSH1 0x1c
                  PUSH2 0x100
                  EXP
                  PUSH2 0x100
                  EXP
                  PUSH1 0x0
                  SSTORE
                  PUSH1 0x1c
                  PUSH1 0xff
                  EXP
                  PUSH2 0x100
                  EXP
                  PUSH1 0x1
                  SSTORE
                  PUSH1 0x1c
                  PUSH2 0x101
                  EXP
                  PUSH2 0x100
                  EXP
                  PUSH1 0x2
                  SSTORE
                  PUSH1 0x1c
                  PUSH2 0x100
                  EXP
                  PUSH1 0xff
                  EXP
                  PUSH1 0x3
                  SSTORE
                  PUSH1 0x1c
                  PUSH1 0xff
                  EXP
                  PUSH1 0xff
                  EXP
                  PUSH1 0x4
                  SSTORE
                  PUSH1 0x1c
                  PUSH2 0x101
                  EXP
                  PUSH1 0xff
                  EXP
                  PUSH1 0x5
                  SSTORE
                  PUSH1 0x1c
                  PUSH2 0x100
                  EXP
                  PUSH2 0x101
                  EXP
                  PUSH1 0x6
                  SSTORE
                  PUSH1 0x1c
                  PUSH1 0xff
                  EXP
                  PUSH2 0x101
                  EXP
                  PUSH1 0x7
                  SSTORE
                  PUSH1 0x1c
                  PUSH2 0x101
                  EXP
                  PUSH2 0x101
                  EXP
                  PUSH1 0x8
                  SSTORE
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
        gaslimit = 10000000
        world = evm.EVMWorld(
            constraints,
            blocknumber=blocknumber,
            timestamp=timestamp,
            difficulty=difficulty,
            coinbase=coinbase,
            gaslimit=gaslimit,
        )

        acc_addr = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        acc_code = unhexlify(
            "601c6101000a6101000a600055601c60ff0a6101000a600155601c6101010a6101000a600255601c6101000a60ff0a600355601c60ff0a60ff0a600455601c6101010a60ff0a600555601c6101000a6101010a600655601c60ff0a6101010a600755601c6101010a6101010a600855"
        )
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F2947DEF4CF144679DA39C4C32BDC35681
        price = 0x5AF3107A4000
        value = 1000000000000000000
        gas = 1000000
        data = ""
        # open a fake tx, no funds send
        world._open_transaction("CALL", address, price, data, caller, value, gas=gas)

        # This variable might seem redundant in some tests - don't forget it is auto generated
        # and there are cases in which we need it ;)
        result, returndata = self._test_run(world)

        # World sanity checks - those should not change, right?
        self.assertEqual(solve(world.block_number()), 0)
        self.assertEqual(solve(world.block_gaslimit()), 10000000)
        self.assertEqual(solve(world.block_timestamp()), 1)
        self.assertEqual(solve(world.block_difficulty()), 256)
        self.assertEqual(solve(world.block_coinbase()), 0x2ADC25665018AA1FE0E6BC666DAC8FC2697FF9BA)

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 0)
        self.assertEqual(
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 1000000000000000000
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6),
            unhexlify(
                "601c6101000a6101000a600055601c60ff0a6101000a600155601c6101010a6101000a600255601c6101000a60ff0a600355601c60ff0a60ff0a600455601c6101010a60ff0a600555601c6101000a6101010a600655601c60ff0a6101010a600755601c6101010a6101010a600855"
            ),
        )
        # check storage
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x03)),
            0x14FF7F0000000000000000000000000000000000000000000000000000000001,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x04)),
            0xFFD368E44B3F85CB81AE394C9809CA9FA2DB46A83D7880A912AB6D4A87E400FF,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x05)),
            0x0981AD53C19B15A94BCF0BF20235DD0DA9DF25F46AE635029FE2062E6C1C00FF,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x06)),
            0x6AFF810000000000000000000000000000000000000000000000000000000001,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x07)),
            0x19DF06FFA28250867006726405FBC05D43DC2F9D2F025006DB089BD46BE40101,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x08)),
            0x243FFFE3A4F2982F45055C08F379648AB886DA8027A7401117A8E0B8881C0101,
        )
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
        self.assertEqual(solve(world.current_vm.gas), 862042)

    def test_expPowerOf256Of256_1(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: expPowerOf256Of256_1.json
        sha256sum: 55ea9d8a3710b200e38f83bbb9622171a99c9d85410b39f0fc319cade6d25913
        Code:     PUSH1 0x1
                  PUSH2 0x100
                  EXP
                  PUSH2 0x100
                  EXP
                  PUSH1 0x0
                  SSTORE
                  PUSH1 0x1
                  PUSH1 0xff
                  EXP
                  PUSH2 0x100
                  EXP
                  PUSH1 0x1
                  SSTORE
                  PUSH1 0x1
                  PUSH2 0x101
                  EXP
                  PUSH2 0x100
                  EXP
                  PUSH1 0x2
                  SSTORE
                  PUSH1 0x1
                  PUSH2 0x100
                  EXP
                  PUSH1 0xff
                  EXP
                  PUSH1 0x3
                  SSTORE
                  PUSH1 0x1
                  PUSH1 0xff
                  EXP
                  PUSH1 0xff
                  EXP
                  PUSH1 0x4
                  SSTORE
                  PUSH1 0x1
                  PUSH2 0x101
                  EXP
                  PUSH1 0xff
                  EXP
                  PUSH1 0x5
                  SSTORE
                  PUSH1 0x1
                  PUSH2 0x100
                  EXP
                  PUSH2 0x101
                  EXP
                  PUSH1 0x6
                  SSTORE
                  PUSH1 0x1
                  PUSH1 0xff
                  EXP
                  PUSH2 0x101
                  EXP
                  PUSH1 0x7
                  SSTORE
                  PUSH1 0x1
                  PUSH2 0x101
                  EXP
                  PUSH2 0x101
                  EXP
                  PUSH1 0x8
                  SSTORE
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
        gaslimit = 10000000
        world = evm.EVMWorld(
            constraints,
            blocknumber=blocknumber,
            timestamp=timestamp,
            difficulty=difficulty,
            coinbase=coinbase,
            gaslimit=gaslimit,
        )

        acc_addr = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        acc_code = unhexlify(
            "60016101000a6101000a600055600160ff0a6101000a60015560016101010a6101000a60025560016101000a60ff0a600355600160ff0a60ff0a60045560016101010a60ff0a60055560016101000a6101010a600655600160ff0a6101010a60075560016101010a6101010a600855"
        )
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F2947DEF4CF144679DA39C4C32BDC35681
        price = 0x5AF3107A4000
        value = 1000000000000000000
        gas = 1000000
        data = ""
        # open a fake tx, no funds send
        world._open_transaction("CALL", address, price, data, caller, value, gas=gas)

        # This variable might seem redundant in some tests - don't forget it is auto generated
        # and there are cases in which we need it ;)
        result, returndata = self._test_run(world)

        # World sanity checks - those should not change, right?
        self.assertEqual(solve(world.block_number()), 0)
        self.assertEqual(solve(world.block_gaslimit()), 10000000)
        self.assertEqual(solve(world.block_timestamp()), 1)
        self.assertEqual(solve(world.block_difficulty()), 256)
        self.assertEqual(solve(world.block_coinbase()), 0x2ADC25665018AA1FE0E6BC666DAC8FC2697FF9BA)

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 0)
        self.assertEqual(
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 1000000000000000000
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6),
            unhexlify(
                "60016101000a6101000a600055600160ff0a6101000a60015560016101010a6101000a60025560016101000a60ff0a600355600160ff0a60ff0a60045560016101010a60ff0a60055560016101000a6101010a600655600160ff0a6101010a60075560016101010a6101010a600855"
            ),
        )
        # check storage
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x03)),
            0x06C3ACD330B959AD6EFABCE6D2D2125E73A88A65A9880D203DDDF5957F7F0001,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x04)),
            0x8F965A06DA0AC41DCB3A34F1D8AB7D8FEE620A94FAA42C395997756B007FFEFF,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x05)),
            0xBCE9265D88A053C18BC229EBFF404C1534E1DB43DE85131DA0179FE9FF8100FF,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x06)),
            0x02B5E9D7A094C19F5EBDD4F2E618F859ED15E4F1F0351F286BF849EB7F810001,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x07)),
            0xC73B7A6F68385C653A24993BB72EEA0E4BA17470816EC658CF9C5BEDFD81FF01,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x08)),
            0xB89FC178355660FE1C92C7D8FF11524702FAD6E2255447946442356B00810101,
        )
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
        self.assertEqual(solve(world.current_vm.gas), 864472)

    def test_expPowerOf256Of256_4(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: expPowerOf256Of256_4.json
        sha256sum: 133369ae88eeb438b9672375fa4f7e3f302d7c76626e068f3a3ab0f00eb803a9
        Code:     PUSH1 0x4
                  PUSH2 0x100
                  EXP
                  PUSH2 0x100
                  EXP
                  PUSH1 0x0
                  SSTORE
                  PUSH1 0x4
                  PUSH1 0xff
                  EXP
                  PUSH2 0x100
                  EXP
                  PUSH1 0x1
                  SSTORE
                  PUSH1 0x4
                  PUSH2 0x101
                  EXP
                  PUSH2 0x100
                  EXP
                  PUSH1 0x2
                  SSTORE
                  PUSH1 0x4
                  PUSH2 0x100
                  EXP
                  PUSH1 0xff
                  EXP
                  PUSH1 0x3
                  SSTORE
                  PUSH1 0x4
                  PUSH1 0xff
                  EXP
                  PUSH1 0xff
                  EXP
                  PUSH1 0x4
                  SSTORE
                  PUSH1 0x4
                  PUSH2 0x101
                  EXP
                  PUSH1 0xff
                  EXP
                  PUSH1 0x5
                  SSTORE
                  PUSH1 0x4
                  PUSH2 0x100
                  EXP
                  PUSH2 0x101
                  EXP
                  PUSH1 0x6
                  SSTORE
                  PUSH1 0x4
                  PUSH1 0xff
                  EXP
                  PUSH2 0x101
                  EXP
                  PUSH1 0x7
                  SSTORE
                  PUSH1 0x4
                  PUSH2 0x101
                  EXP
                  PUSH2 0x101
                  EXP
                  PUSH1 0x8
                  SSTORE
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
        gaslimit = 10000000
        world = evm.EVMWorld(
            constraints,
            blocknumber=blocknumber,
            timestamp=timestamp,
            difficulty=difficulty,
            coinbase=coinbase,
            gaslimit=gaslimit,
        )

        acc_addr = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        acc_code = unhexlify(
            "60046101000a6101000a600055600460ff0a6101000a60015560046101010a6101000a60025560046101000a60ff0a600355600460ff0a60ff0a60045560046101010a60ff0a60055560046101000a6101010a600655600460ff0a6101010a60075560046101010a6101010a600855"
        )
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F2947DEF4CF144679DA39C4C32BDC35681
        price = 0x5AF3107A4000
        value = 1000000000000000000
        gas = 1000000
        data = ""
        # open a fake tx, no funds send
        world._open_transaction("CALL", address, price, data, caller, value, gas=gas)

        # This variable might seem redundant in some tests - don't forget it is auto generated
        # and there are cases in which we need it ;)
        result, returndata = self._test_run(world)

        # World sanity checks - those should not change, right?
        self.assertEqual(solve(world.block_number()), 0)
        self.assertEqual(solve(world.block_gaslimit()), 10000000)
        self.assertEqual(solve(world.block_timestamp()), 1)
        self.assertEqual(solve(world.block_difficulty()), 256)
        self.assertEqual(solve(world.block_coinbase()), 0x2ADC25665018AA1FE0E6BC666DAC8FC2697FF9BA)

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 0)
        self.assertEqual(
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 1000000000000000000
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6),
            unhexlify(
                "60046101000a6101000a600055600460ff0a6101000a60015560046101010a6101000a60025560046101000a60ff0a600355600460ff0a60ff0a60045560046101010a60ff0a60055560046101000a6101010a600655600460ff0a6101010a60075560046101010a6101010a600855"
            ),
        )
        # check storage
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x03)),
            0xE6540CE46EAF70DA9D644015A661E0E245B13F307CB3885514FF7F0000000001,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x04)),
            0x6526B38B05A6325B80E1C84AB41DC934FD70F33F1BD0EAB3D1F61A4707FC00FF,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x05)),
            0xE959516CD27E5D8FD487B72DB2989B3EC2BA9FB7EAD41554526FE5A3040400FF,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x06)),
            0xE7498A48C6CE2530BBE814EE3440C8C44FFFAB7AD8A277AA6AFF810000000001,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x07)),
            0x2DFFA3E901E5A392D15B79F4193D2168147D2AA7C55870B46C3A905D03FC0101,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x08)),
            0xE16EA721C96539EDB4F7FB82DE0DAD8CCCB1E7A6966A6777635F6FB908040101,
        )
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
        self.assertEqual(solve(world.current_vm.gas), 864202)

    def test_smod8_byZero(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: smod8_byZero.json
        sha256sum: bcee748f666d726f3cd0b0d6a76b8c9029e4719aba2a34e8bd59bf1b4c235a49
        Code:     PUSH1 0xd
                  PUSH1 0x0
                  PUSH1 0xc8
                  PUSH1 0x0
                  SUB
                  SMOD
                  SUB
                  PUSH1 0x0
                  SSTORE
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
        acc_code = unhexlify("600d600060c86000030703600055")
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F2947DEF4CF144679DA39C4C32BDC35681
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

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 0)
        self.assertEqual(
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 1000000000000000000
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6),
            unhexlify("600d600060c86000030703600055"),
        )
        # check storage
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x00)),
            0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF3,
        )
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
        self.assertEqual(solve(world.current_vm.gas), 79974)

    def test_smod6(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: smod6.json
        sha256sum: abeb4b71ca1ccd7c9974d0a121c211ceb82091231ce00c38e93832c1fa0b38af
        Code:     PUSH32 0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
                  PUSH32 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
                  PUSH1 0x0
                  SUB
                  SMOD
                  PUSH1 0x0
                  SSTORE
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
        acc_code = unhexlify(
            "7f7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff60000307600055"
        )
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F2947DEF4CF144679DA39C4C32BDC35681
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

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 0)
        self.assertEqual(
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 1000000000000000000
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6),
            unhexlify(
                "7f7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff60000307600055"
            ),
        )
        # check storage
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x00)), 0x01
        )
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
        self.assertEqual(solve(world.current_vm.gas), 79980)

    def test_expPowerOf256Of256_33(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: expPowerOf256Of256_33.json
        sha256sum: 8f763116e64155dbe53aaf5f769a7daf990afb49965141af4cc8ca4fa9b9e4e4
        Code:     PUSH1 0x21
                  PUSH2 0x100
                  EXP
                  PUSH2 0x100
                  EXP
                  PUSH1 0x0
                  SSTORE
                  PUSH1 0x21
                  PUSH1 0xff
                  EXP
                  PUSH2 0x100
                  EXP
                  PUSH1 0x1
                  SSTORE
                  PUSH1 0x21
                  PUSH2 0x101
                  EXP
                  PUSH2 0x100
                  EXP
                  PUSH1 0x2
                  SSTORE
                  PUSH1 0x21
                  PUSH2 0x100
                  EXP
                  PUSH1 0xff
                  EXP
                  PUSH1 0x3
                  SSTORE
                  PUSH1 0x21
                  PUSH1 0xff
                  EXP
                  PUSH1 0xff
                  EXP
                  PUSH1 0x4
                  SSTORE
                  PUSH1 0x21
                  PUSH2 0x101
                  EXP
                  PUSH1 0xff
                  EXP
                  PUSH1 0x5
                  SSTORE
                  PUSH1 0x21
                  PUSH2 0x100
                  EXP
                  PUSH2 0x101
                  EXP
                  PUSH1 0x6
                  SSTORE
                  PUSH1 0x21
                  PUSH1 0xff
                  EXP
                  PUSH2 0x101
                  EXP
                  PUSH1 0x7
                  SSTORE
                  PUSH1 0x21
                  PUSH2 0x101
                  EXP
                  PUSH2 0x101
                  EXP
                  PUSH1 0x8
                  SSTORE
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
        gaslimit = 10000000
        world = evm.EVMWorld(
            constraints,
            blocknumber=blocknumber,
            timestamp=timestamp,
            difficulty=difficulty,
            coinbase=coinbase,
            gaslimit=gaslimit,
        )

        acc_addr = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        acc_code = unhexlify(
            "60216101000a6101000a600055602160ff0a6101000a60015560216101010a6101000a60025560216101000a60ff0a600355602160ff0a60ff0a60045560216101010a60ff0a60055560216101000a6101010a600655602160ff0a6101010a60075560216101010a6101010a600855"
        )
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F2947DEF4CF144679DA39C4C32BDC35681
        price = 0x5AF3107A4000
        value = 1000000000000000000
        gas = 1000000
        data = ""
        # open a fake tx, no funds send
        world._open_transaction("CALL", address, price, data, caller, value, gas=gas)

        # This variable might seem redundant in some tests - don't forget it is auto generated
        # and there are cases in which we need it ;)
        result, returndata = self._test_run(world)

        # World sanity checks - those should not change, right?
        self.assertEqual(solve(world.block_number()), 0)
        self.assertEqual(solve(world.block_gaslimit()), 10000000)
        self.assertEqual(solve(world.block_timestamp()), 1)
        self.assertEqual(solve(world.block_difficulty()), 256)
        self.assertEqual(solve(world.block_coinbase()), 0x2ADC25665018AA1FE0E6BC666DAC8FC2697FF9BA)

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 0)
        self.assertEqual(
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 1000000000000000000
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6),
            unhexlify(
                "60216101000a6101000a600055602160ff0a6101000a60015560216101010a6101000a60025560216101000a60ff0a600355602160ff0a60ff0a60045560216101010a60ff0a60055560216101000a6101010a600655602160ff0a6101010a60075560216101010a6101010a600855"
            ),
        )
        # check storage
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x00)), 0x01
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x03)), 0x01
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x04)),
            0x8DCB65B5494EBA78CD6756A6F9851F6E26D0F2BB9ECD7E9ABD7E9B11209FFEFF,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x05)),
            0x6694BB31B20CD625F3756897DAE6D738F2E64467B5B6F10FA3E07763FFA100FF,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x06)), 0x01
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x07)),
            0xE678999AEFFD1F1F45081F64DE7F80AB083DD7DF04721ED64EE04C03BDA1FF01,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x08)),
            0x39B68FB9898DD7568ABD178397251CE8226A25C1D305A4E79573333520A10101,
        )
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
        self.assertEqual(solve(world.current_vm.gas), 847702)

    def test_expXY_success(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: expXY_success.json
        sha256sum: a9d554c77e7cbb0bf5374f68f128fe84f896bb0996e3fc56d935fcc3d243a0e4
        Code:     PUSH1 0x0
                  CALLDATALOAD
                  PUSH1 0x0
                  SSTORE
                  PUSH1 0x20
                  CALLDATALOAD
                  PUSH1 0x1
                  SSTORE
                  PUSH1 0x1
                  SLOAD
                  PUSH1 0x0
                  SLOAD
                  EXP
                  PUSH1 0x2
                  SSTORE
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
        acc_code = unhexlify("6000356000556020356001556001546000540a600255")
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F2947DEF4CF144679DA39C4C32BDC35681
        price = 0x5AF3107A4000
        value = 1000000000000000000
        gas = 100000
        data = b"\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x02\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x0f"
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

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 0)
        self.assertEqual(
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 1000000000000000000
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6),
            unhexlify("6000356000556020356001556001546000540a600255"),
        )
        # check storage
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x00)), 0x02
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x01)), 0x0F
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x02)), 0x8000
        )
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
        self.assertEqual(solve(world.current_vm.gas), 39853)

    def test_addmod1_overflow2(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: addmod1_overflow2.json
        sha256sum: 6d53e0173a8759687a942922b766aadd9a24b71eec1469b4fed17d2783b18a9b
        Code:     PUSH1 0x5
                  PUSH1 0x0
                  PUSH1 0x1
                  PUSH1 0x0
                  SUB
                  ADDMOD
                  PUSH1 0x0
                  SSTORE
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
        acc_code = unhexlify("60056000600160000308600055")
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F2947DEF4CF144679DA39C4C32BDC35681
        price = 0x5AF3107A4000
        value = 1000000000000000000
        gas = 10000
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

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 0)
        self.assertEqual(
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 1000000000000000000
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6),
            unhexlify("60056000600160000308600055"),
        )
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
        self.assertEqual(solve(world.current_vm.gas), 4974)

    def test_mul5(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: mul5.json
        sha256sum: 27e7f51bca0b7069694d12c59d43003cef22ec0ecf0309aa28ec47ca3911db95
        Code:     PUSH32 0x8000000000000000000000000000000000000000000000000000000000000000
                  PUSH32 0x8000000000000000000000000000000000000000000000000000000000000000
                  MUL
                  PUSH1 0x0
                  SSTORE
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
        acc_code = unhexlify(
            "7f80000000000000000000000000000000000000000000000000000000000000007f800000000000000000000000000000000000000000000000000000000000000002600055"
        )
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F2947DEF4CF144679DA39C4C32BDC35681
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

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 0)
        self.assertEqual(
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 1000000000000000000
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6),
            unhexlify(
                "7f80000000000000000000000000000000000000000000000000000000000000007f800000000000000000000000000000000000000000000000000000000000000002600055"
            ),
        )
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
        self.assertEqual(solve(world.current_vm.gas), 94986)

    def test_expPowerOf256Of256_9(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: expPowerOf256Of256_9.json
        sha256sum: 773dd1eb4eed06df60aea02095374c3442a0b521cb90605e85a8a6bfbce5ef2b
        Code:     PUSH1 0x9
                  PUSH2 0x100
                  EXP
                  PUSH2 0x100
                  EXP
                  PUSH1 0x0
                  SSTORE
                  PUSH1 0x9
                  PUSH1 0xff
                  EXP
                  PUSH2 0x100
                  EXP
                  PUSH1 0x1
                  SSTORE
                  PUSH1 0x9
                  PUSH2 0x101
                  EXP
                  PUSH2 0x100
                  EXP
                  PUSH1 0x2
                  SSTORE
                  PUSH1 0x9
                  PUSH2 0x100
                  EXP
                  PUSH1 0xff
                  EXP
                  PUSH1 0x3
                  SSTORE
                  PUSH1 0x9
                  PUSH1 0xff
                  EXP
                  PUSH1 0xff
                  EXP
                  PUSH1 0x4
                  SSTORE
                  PUSH1 0x9
                  PUSH2 0x101
                  EXP
                  PUSH1 0xff
                  EXP
                  PUSH1 0x5
                  SSTORE
                  PUSH1 0x9
                  PUSH2 0x100
                  EXP
                  PUSH2 0x101
                  EXP
                  PUSH1 0x6
                  SSTORE
                  PUSH1 0x9
                  PUSH1 0xff
                  EXP
                  PUSH2 0x101
                  EXP
                  PUSH1 0x7
                  SSTORE
                  PUSH1 0x9
                  PUSH2 0x101
                  EXP
                  PUSH2 0x101
                  EXP
                  PUSH1 0x8
                  SSTORE
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
        gaslimit = 10000000
        world = evm.EVMWorld(
            constraints,
            blocknumber=blocknumber,
            timestamp=timestamp,
            difficulty=difficulty,
            coinbase=coinbase,
            gaslimit=gaslimit,
        )

        acc_addr = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        acc_code = unhexlify(
            "60096101000a6101000a600055600960ff0a6101000a60015560096101010a6101000a60025560096101000a60ff0a600355600960ff0a60ff0a60045560096101010a60ff0a60055560096101000a6101010a600655600960ff0a6101010a60075560096101010a6101010a600855"
        )
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F2947DEF4CF144679DA39C4C32BDC35681
        price = 0x5AF3107A4000
        value = 1000000000000000000
        gas = 1000000
        data = ""
        # open a fake tx, no funds send
        world._open_transaction("CALL", address, price, data, caller, value, gas=gas)

        # This variable might seem redundant in some tests - don't forget it is auto generated
        # and there are cases in which we need it ;)
        result, returndata = self._test_run(world)

        # World sanity checks - those should not change, right?
        self.assertEqual(solve(world.block_number()), 0)
        self.assertEqual(solve(world.block_gaslimit()), 10000000)
        self.assertEqual(solve(world.block_timestamp()), 1)
        self.assertEqual(solve(world.block_difficulty()), 256)
        self.assertEqual(solve(world.block_coinbase()), 0x2ADC25665018AA1FE0E6BC666DAC8FC2697FF9BA)

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 0)
        self.assertEqual(
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 1000000000000000000
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6),
            unhexlify(
                "60096101000a6101000a600055600960ff0a6101000a60015560096101010a6101000a60025560096101000a60ff0a600355600960ff0a60ff0a60045560096101010a60ff0a60055560096101000a6101010a600655600960ff0a6101010a60075560096101010a6101010a600855"
            ),
        )
        # check storage
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x03)),
            0x53017D8EB210DB2C8CD4A299079EC55C33085514FF7F00000000000000000001,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x04)),
            0x48BE09B6C6AE2AA660F1972125CECBB1038B5D236ECF766BA786E2C4E887FEFF,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x05)),
            0x2E350D847BA73DC2099F83F532951C47269D9FD7E411B50BAE00A9581F8900FF,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x06)),
            0x013AB9E1F0DF89A184B4D07080B68FB921F7AA6AFF8100000000000000000001,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x07)),
            0xF387ED41C1050F9DA667F429A3E8FB30B61A55EDE97D7B8ACD797A03CD89FF01,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x08)),
            0x525696C22BB3CE00FD2E3F6BBB9B4EA1046A5E31FCFF2FEDF8F8C74D28890101,
        )
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
        self.assertEqual(solve(world.current_vm.gas), 863752)

    def test_expPowerOf256Of256_20(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: expPowerOf256Of256_20.json
        sha256sum: 773b8ea18b482afbe1c50d8c7fcb12789d399fa1e316d72319f653e8150c7f7e
        Code:     PUSH1 0x14
                  PUSH2 0x100
                  EXP
                  PUSH2 0x100
                  EXP
                  PUSH1 0x0
                  SSTORE
                  PUSH1 0x14
                  PUSH1 0xff
                  EXP
                  PUSH2 0x100
                  EXP
                  PUSH1 0x1
                  SSTORE
                  PUSH1 0x14
                  PUSH2 0x101
                  EXP
                  PUSH2 0x100
                  EXP
                  PUSH1 0x2
                  SSTORE
                  PUSH1 0x14
                  PUSH2 0x100
                  EXP
                  PUSH1 0xff
                  EXP
                  PUSH1 0x3
                  SSTORE
                  PUSH1 0x14
                  PUSH1 0xff
                  EXP
                  PUSH1 0xff
                  EXP
                  PUSH1 0x4
                  SSTORE
                  PUSH1 0x14
                  PUSH2 0x101
                  EXP
                  PUSH1 0xff
                  EXP
                  PUSH1 0x5
                  SSTORE
                  PUSH1 0x14
                  PUSH2 0x100
                  EXP
                  PUSH2 0x101
                  EXP
                  PUSH1 0x6
                  SSTORE
                  PUSH1 0x14
                  PUSH1 0xff
                  EXP
                  PUSH2 0x101
                  EXP
                  PUSH1 0x7
                  SSTORE
                  PUSH1 0x14
                  PUSH2 0x101
                  EXP
                  PUSH2 0x101
                  EXP
                  PUSH1 0x8
                  SSTORE
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
        gaslimit = 10000000
        world = evm.EVMWorld(
            constraints,
            blocknumber=blocknumber,
            timestamp=timestamp,
            difficulty=difficulty,
            coinbase=coinbase,
            gaslimit=gaslimit,
        )

        acc_addr = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        acc_code = unhexlify(
            "60146101000a6101000a600055601460ff0a6101000a60015560146101010a6101000a60025560146101000a60ff0a600355601460ff0a60ff0a60045560146101010a60ff0a60055560146101000a6101010a600655601460ff0a6101010a60075560146101010a6101010a600855"
        )
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F2947DEF4CF144679DA39C4C32BDC35681
        price = 0x5AF3107A4000
        value = 1000000000000000000
        gas = 1000000
        data = ""
        # open a fake tx, no funds send
        world._open_transaction("CALL", address, price, data, caller, value, gas=gas)

        # This variable might seem redundant in some tests - don't forget it is auto generated
        # and there are cases in which we need it ;)
        result, returndata = self._test_run(world)

        # World sanity checks - those should not change, right?
        self.assertEqual(solve(world.block_number()), 0)
        self.assertEqual(solve(world.block_gaslimit()), 10000000)
        self.assertEqual(solve(world.block_timestamp()), 1)
        self.assertEqual(solve(world.block_difficulty()), 256)
        self.assertEqual(solve(world.block_coinbase()), 0x2ADC25665018AA1FE0E6BC666DAC8FC2697FF9BA)

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 0)
        self.assertEqual(
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 1000000000000000000
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6),
            unhexlify(
                "60146101000a6101000a600055601460ff0a6101000a60015560146101010a6101000a60025560146101000a60ff0a600355601460ff0a60ff0a60045560146101010a60ff0a60055560146101000a6101010a600655601460ff0a6101010a60075560146101010a6101010a600855"
            ),
        )
        # check storage
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x03)),
            0x18879EC55C33085514FF7F000000000000000000000000000000000000000001,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x04)),
            0x67E4797DC21F02CE4A7C52218C7DBEA5D212E6C244E24F0BA4C08613C7EC00FF,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x05)),
            0xA1CE1A085F258785846939CC1D2E8725AC94AD4DFF8913234E00679FB41400FF,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x06)),
            0xF000B68FB921F7AA6AFF81000000000000000000000000000000000000000001,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x07)),
            0xCCE501857A1CB45473915A28082AF950E0F78F7E2DE68CE748ADB661B3EC0101,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x08)),
            0x3B2E28D274A16C08B58A23BAD63BBA6D7B09685769D1F68CA3873BEDC8140101,
        )
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
        self.assertEqual(solve(world.current_vm.gas), 862762)

    def test_expPowerOf256_23(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: expPowerOf256_23.json
        sha256sum: 8320b29b9626226680d60fc6f959fcea0fafe174a5cfd5e9725745291797af15
        Code:     PUSH1 0x17
                  PUSH2 0x100
                  EXP
                  PUSH1 0x0
                  SSTORE
                  PUSH1 0x17
                  PUSH1 0xff
                  EXP
                  PUSH1 0x1
                  SSTORE
                  PUSH1 0x17
                  PUSH2 0x101
                  EXP
                  PUSH1 0x2
                  SSTORE
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
        acc_code = unhexlify("60176101000a600055601760ff0a60015560176101010a600255")
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F2947DEF4CF144679DA39C4C32BDC35681
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

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 0)
        self.assertEqual(
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 1000000000000000000
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6),
            unhexlify("60176101000a600055601760ff0a60015560176101010a600255"),
        )
        # check storage
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x00)),
            0x010000000000000000000000000000000000000000000000,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x01)),
            0xE9F63715159CC9E33A7502256EAE721B304E6FEA0316FF,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x02)),
            0x0118040E1BFF182CD3AFB8410F81A5092FD6939DEBFD1701,
        )
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
        self.assertEqual(solve(world.current_vm.gas), 39913)

    def test_expPowerOf2_16(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: expPowerOf2_16.json
        sha256sum: 2c3a71539fc95229e67a05630611ee85e45c8441f0d517da8a25d68b873da3f0
        Code:     PUSH1 0x10
                  PUSH1 0x2
                  EXP
                  PUSH1 0x0
                  SSTORE
                  PUSH1 0xf
                  PUSH1 0x2
                  EXP
                  PUSH1 0x1
                  SSTORE
                  PUSH1 0x11
                  PUSH1 0x2
                  EXP
                  PUSH1 0x2
                  SSTORE
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
        acc_code = unhexlify("601060020a600055600f60020a600155601160020a600255")
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F2947DEF4CF144679DA39C4C32BDC35681
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

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 0)
        self.assertEqual(
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 1000000000000000000
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6),
            unhexlify("601060020a600055600f60020a600155601160020a600255"),
        )
        # check storage
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x00)), 0x010000
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x01)), 0x8000
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x02)), 0x020000
        )
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
        self.assertEqual(solve(world.current_vm.gas), 39913)

    def test_expPowerOf2_2(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: expPowerOf2_2.json
        sha256sum: b7e6ef69b571deadf273428a2ea22d73701409e6bfc2813874bfe7ba12687737
        Code:     PUSH1 0x2
                  PUSH1 0x2
                  EXP
                  PUSH1 0x0
                  SSTORE
                  PUSH1 0x1
                  PUSH1 0x2
                  EXP
                  PUSH1 0x1
                  SSTORE
                  PUSH1 0x3
                  PUSH1 0x2
                  EXP
                  PUSH1 0x2
                  SSTORE
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
        acc_code = unhexlify("600260020a600055600160020a600155600360020a600255")
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F2947DEF4CF144679DA39C4C32BDC35681
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

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 0)
        self.assertEqual(
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 1000000000000000000
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6),
            unhexlify("600260020a600055600160020a600155600360020a600255"),
        )
        # check storage
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x00)), 0x04
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x01)), 0x02
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x02)), 0x08
        )
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
        self.assertEqual(solve(world.current_vm.gas), 39913)

    def test_expPowerOf256_7(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: expPowerOf256_7.json
        sha256sum: 61b989ba296e526bbd98acd3e0defc772990afbbaa232b82ebd8ea225b8e5a8b
        Code:     PUSH1 0x7
                  PUSH2 0x100
                  EXP
                  PUSH1 0x0
                  SSTORE
                  PUSH1 0x7
                  PUSH1 0xff
                  EXP
                  PUSH1 0x1
                  SSTORE
                  PUSH1 0x7
                  PUSH2 0x101
                  EXP
                  PUSH1 0x2
                  SSTORE
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
        acc_code = unhexlify("60076101000a600055600760ff0a60015560076101010a600255")
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F2947DEF4CF144679DA39C4C32BDC35681
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

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 0)
        self.assertEqual(
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 1000000000000000000
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6),
            unhexlify("60076101000a600055600760ff0a60015560076101010a600255"),
        )
        # check storage
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x00)),
            0x0100000000000000,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x01)),
            0xF914DD22EB06FF,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x02)),
            0x0107152323150701,
        )
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
        self.assertEqual(solve(world.current_vm.gas), 39913)

    def test_expPowerOf256_16(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: expPowerOf256_16.json
        sha256sum: b3912160e11fd495497ba6bc62cc649cf5572048412234be7b2a023d298a14c7
        Code:     PUSH1 0x10
                  PUSH2 0x100
                  EXP
                  PUSH1 0x0
                  SSTORE
                  PUSH1 0x10
                  PUSH1 0xff
                  EXP
                  PUSH1 0x1
                  SSTORE
                  PUSH1 0x10
                  PUSH2 0x101
                  EXP
                  PUSH1 0x2
                  SSTORE
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
        acc_code = unhexlify("60106101000a600055601060ff0a60015560106101010a600255")
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F2947DEF4CF144679DA39C4C32BDC35681
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

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 0)
        self.assertEqual(
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 1000000000000000000
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6),
            unhexlify("60106101000a600055601060ff0a60015560106101010a600255"),
        )
        # check storage
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x00)),
            0x0100000000000000000000000000000000,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x01)),
            0xF075D70B0F1B82196F36F719D077F001,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x02)),
            0x01107A372D2F74E272CF59171E30781001,
        )
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
        self.assertEqual(solve(world.current_vm.gas), 39913)

    def test_add0(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: add0.json
        sha256sum: 1b9624ff5644c08e974d19fb58b8b2a42b61dcf46f906b86d0794ea7ec0b2345
        Code:     PUSH32 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
                  PUSH32 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
                  ADD
                  PUSH1 0x0
                  SSTORE
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
        acc_code = unhexlify(
            "7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff01600055"
        )
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F2947DEF4CF144679DA39C4C32BDC35681
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

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 0)
        self.assertEqual(
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 1000000000000000000
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6),
            unhexlify(
                "7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff01600055"
            ),
        )
        # check storage
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x00)),
            0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFE,
        )
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
        self.assertEqual(solve(world.current_vm.gas), 79988)

    def test_expPowerOf2_32(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: expPowerOf2_32.json
        sha256sum: 1ca89c3edda3c9290247d3da6f3a3b03037059a015b70973ee54d690913bef25
        Code:     PUSH1 0x20
                  PUSH1 0x2
                  EXP
                  PUSH1 0x0
                  SSTORE
                  PUSH1 0x1f
                  PUSH1 0x2
                  EXP
                  PUSH1 0x1
                  SSTORE
                  PUSH1 0x21
                  PUSH1 0x2
                  EXP
                  PUSH1 0x2
                  SSTORE
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
        acc_code = unhexlify("602060020a600055601f60020a600155602160020a600255")
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F2947DEF4CF144679DA39C4C32BDC35681
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

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 0)
        self.assertEqual(
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 1000000000000000000
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6),
            unhexlify("602060020a600055601f60020a600155602160020a600255"),
        )
        # check storage
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x00)),
            0x0100000000,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x01)),
            0x80000000,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x02)),
            0x0200000000,
        )
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
        self.assertEqual(solve(world.current_vm.gas), 39913)

    def test_mulmod1_overflow2(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: mulmod1_overflow2.json
        sha256sum: 9361ad1f015dcd2ff73fc319d3615689948a8cff5b1d693cbcb23b992a1f90db
        Code:     PUSH1 0x5
                  PUSH1 0x2
                  PUSH32 0x8000000000000000000000000000000000000000000000000000000000000000
                  MULMOD
                  PUSH1 0x0
                  SSTORE
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
        acc_code = unhexlify(
            "600560027f800000000000000000000000000000000000000000000000000000000000000009600055"
        )
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F2947DEF4CF144679DA39C4C32BDC35681
        price = 0x5AF3107A4000
        value = 1000000000000000000
        gas = 1000000
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

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 0)
        self.assertEqual(
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 1000000000000000000
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6),
            unhexlify(
                "600560027f800000000000000000000000000000000000000000000000000000000000000009600055"
            ),
        )
        # check storage
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x00)), 0x01
        )
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
        self.assertEqual(solve(world.current_vm.gas), 979980)

    def test_expPowerOf256_6(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: expPowerOf256_6.json
        sha256sum: f39c9e78e0c492a5537cd763021a18d8b6cd79762a964e3103fc215e215daa38
        Code:     PUSH1 0x6
                  PUSH2 0x100
                  EXP
                  PUSH1 0x0
                  SSTORE
                  PUSH1 0x6
                  PUSH1 0xff
                  EXP
                  PUSH1 0x1
                  SSTORE
                  PUSH1 0x6
                  PUSH2 0x101
                  EXP
                  PUSH1 0x2
                  SSTORE
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
        acc_code = unhexlify("60066101000a600055600660ff0a60015560066101010a600255")
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F2947DEF4CF144679DA39C4C32BDC35681
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

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 0)
        self.assertEqual(
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 1000000000000000000
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6),
            unhexlify("60066101000a600055600660ff0a60015560066101010a600255"),
        )
        # check storage
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x00)),
            0x01000000000000,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x01)),
            0xFA0EEC0EFA01,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x02)),
            0x01060F140F0601,
        )
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
        self.assertEqual(solve(world.current_vm.gas), 39913)

    def test_addmodBigIntCast(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: addmodBigIntCast.json
        sha256sum: 241ccaee5295d1b7015b0c489f5463d7be34619033e089550a114e191782242b
        Code:     PUSH1 0x5
                  PUSH1 0x1
                  PUSH32 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
                  ADDMOD
                  PUSH1 0x0
                  SSTORE
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
        acc_code = unhexlify(
            "600560017fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff08600055"
        )
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F2947DEF4CF144679DA39C4C32BDC35681
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

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 0)
        self.assertEqual(
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 1000000000000000000
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6),
            unhexlify(
                "600560017fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff08600055"
            ),
        )
        # check storage
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x00)), 0x01
        )
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
        self.assertEqual(solve(world.current_vm.gas), 79980)

    def test_signextend_bigBytePlus1(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: signextend_bigBytePlus1.json
        sha256sum: c0e78b1d5a7d5a0aa6d620252bc5d3e2f90da0570222ed61a1f7ec33a2e9b0a3
        Code:     PUSH7 0xf0000000000001
                  PUSH2 0xffff
                  SIGNEXTEND
                  PUSH1 0x0
                  SSTORE
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
        gaslimit = 10000000
        world = evm.EVMWorld(
            constraints,
            blocknumber=blocknumber,
            timestamp=timestamp,
            difficulty=difficulty,
            coinbase=coinbase,
            gaslimit=gaslimit,
        )

        acc_addr = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        acc_code = unhexlify("66f000000000000161ffff0b600055")
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F2947DEF4CF144679DA39C4C32BDC35681
        price = 0x5AF3107A4000
        value = 1000000000000000000
        gas = 1000000
        data = ""
        # open a fake tx, no funds send
        world._open_transaction("CALL", address, price, data, caller, value, gas=gas)

        # This variable might seem redundant in some tests - don't forget it is auto generated
        # and there are cases in which we need it ;)
        result, returndata = self._test_run(world)

        # World sanity checks - those should not change, right?
        self.assertEqual(solve(world.block_number()), 0)
        self.assertEqual(solve(world.block_gaslimit()), 10000000)
        self.assertEqual(solve(world.block_timestamp()), 1)
        self.assertEqual(solve(world.block_difficulty()), 256)
        self.assertEqual(solve(world.block_coinbase()), 0x2ADC25665018AA1FE0E6BC666DAC8FC2697FF9BA)

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 0)
        self.assertEqual(
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 1000000000000000000
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6),
            unhexlify("66f000000000000161ffff0b600055"),
        )
        # check storage
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x00)),
            0xF0000000000001,
        )
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
        self.assertEqual(solve(world.current_vm.gas), 979986)

    def test_signextend_BigBytePlus1_2(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: signextend_BigBytePlus1_2.json
        sha256sum: 2d4f4db0b8cce0abc97e9b4a0d771f58cc4c02dd522c0a87468eefb3236d9db3
        Code:     PUSH1 0xff
                  PUSH9 0xf00000000000000001
                  SIGNEXTEND
                  PUSH1 0x0
                  SSTORE
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
        gaslimit = 10000000
        world = evm.EVMWorld(
            constraints,
            blocknumber=blocknumber,
            timestamp=timestamp,
            difficulty=difficulty,
            coinbase=coinbase,
            gaslimit=gaslimit,
        )

        acc_addr = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        acc_code = unhexlify("60ff68f000000000000000010b600055")
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F2947DEF4CF144679DA39C4C32BDC35681
        price = 0x5AF3107A4000
        value = 1000000000000000000
        gas = 1000000
        data = ""
        # open a fake tx, no funds send
        world._open_transaction("CALL", address, price, data, caller, value, gas=gas)

        # This variable might seem redundant in some tests - don't forget it is auto generated
        # and there are cases in which we need it ;)
        result, returndata = self._test_run(world)

        # World sanity checks - those should not change, right?
        self.assertEqual(solve(world.block_number()), 0)
        self.assertEqual(solve(world.block_gaslimit()), 10000000)
        self.assertEqual(solve(world.block_timestamp()), 1)
        self.assertEqual(solve(world.block_difficulty()), 256)
        self.assertEqual(solve(world.block_coinbase()), 0x2ADC25665018AA1FE0E6BC666DAC8FC2697FF9BA)

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 0)
        self.assertEqual(
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 1000000000000000000
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6),
            unhexlify("60ff68f000000000000000010b600055"),
        )
        # check storage
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x00)), 0xFF
        )
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
        self.assertEqual(solve(world.current_vm.gas), 979986)

    def test_expPowerOf256_22(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: expPowerOf256_22.json
        sha256sum: 13cfb8aaf7225968816d16a4431dec7b1450c365dd74bb1d5e77964ce04d8907
        Code:     PUSH1 0x16
                  PUSH2 0x100
                  EXP
                  PUSH1 0x0
                  SSTORE
                  PUSH1 0x16
                  PUSH1 0xff
                  EXP
                  PUSH1 0x1
                  SSTORE
                  PUSH1 0x16
                  PUSH2 0x101
                  EXP
                  PUSH1 0x2
                  SSTORE
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
        acc_code = unhexlify("60166101000a600055601660ff0a60015560166101010a600255")
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F2947DEF4CF144679DA39C4C32BDC35681
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

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 0)
        self.assertEqual(
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 1000000000000000000
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6),
            unhexlify("60166101000a600055601660ff0a60015560166101010a600255"),
        )
        # check storage
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x00)),
            0x0100000000000000000000000000000000000000000000,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x01)),
            0xEAE1182D42DFA98CC73C3E63D280F30E3E8CFCE6EA01,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x02)),
            0x0116ED20FB041418BAF4C37D91EFB553DBFA9904E71601,
        )
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
        self.assertEqual(solve(world.current_vm.gas), 39913)

    def test_expPowerOf256_24(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: expPowerOf256_24.json
        sha256sum: 4aff8ff31080a4d5830af3c8497e69283cca7f730be72f1014e75246aaa435fc
        Code:     PUSH1 0x18
                  PUSH2 0x100
                  EXP
                  PUSH1 0x0
                  SSTORE
                  PUSH1 0x18
                  PUSH1 0xff
                  EXP
                  PUSH1 0x1
                  SSTORE
                  PUSH1 0x18
                  PUSH2 0x101
                  EXP
                  PUSH1 0x2
                  SSTORE
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
        acc_code = unhexlify("60186101000a600055601860ff0a60015560186101010a600255")
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F2947DEF4CF144679DA39C4C32BDC35681
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

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 0)
        self.assertEqual(
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 1000000000000000000
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6),
            unhexlify("60186101000a600055601860ff0a60015560186101010a600255"),
        )
        # check storage
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x00)),
            0x01000000000000000000000000000000000000000000000000,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x01)),
            0xE90C40DE00872D19573A8D23493FC3A9151E217A1913E801,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x02)),
            0x01191C122A1B1745008367F9509126AE39066A3189E9141801,
        )
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
        self.assertEqual(solve(world.current_vm.gas), 39913)

    def test_mul6(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: mul6.json
        sha256sum: da2592cf38ec886ab0db85c44bffe2d200dc276fc6ff595ee4c012304e96c496
        Code:     PUSH32 0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
                  PUSH32 0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
                  MUL
                  PUSH1 0x0
                  SSTORE
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
        acc_code = unhexlify(
            "7f7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7f7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff02600055"
        )
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F2947DEF4CF144679DA39C4C32BDC35681
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

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 0)
        self.assertEqual(
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 1000000000000000000
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6),
            unhexlify(
                "7f7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7f7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff02600055"
            ),
        )
        # check storage
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x00)), 0x01
        )
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
        self.assertEqual(solve(world.current_vm.gas), 79986)

    def test_fibbonacci_unrolled(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: fibbonacci_unrolled.json
        sha256sum: 96a4a7bcd1eed854a2d0778c706de18fb99bcd359834fe818b6eaed74afc3dcd
        Code:     PUSH1 0x1
                  PUSH1 0x1
                  DUP2
                  DUP2
                  ADD
                  DUP2
                  DUP2
                  ADD
                  DUP2
                  DUP2
                  ADD
                  DUP2
                  DUP2
                  ADD
                  DUP2
                  DUP2
                  ADD
                  DUP2
                  DUP2
                  ADD
                  DUP2
                  DUP2
                  ADD
                  DUP2
                  DUP2
                  ADD
                  DUP2
                  DUP2
                  ADD
                  DUP2
                  DUP2
                  ADD
                  DUP2
                  DUP2
                  ADD
                  DUP2
                  DUP2
                  ADD
                  DUP2
                  DUP2
                  ADD
                  DUP2
                  DUP2
                  ADD
                  DUP2
                  DUP2
                  ADD
                  DUP2
                  DUP2
                  ADD
                  DUP2
                  DUP2
                  ADD
                  PUSH1 0x0
                  MSTORE
                  PUSH1 0x20
                  PUSH1 0x0
                  RETURN
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
        gaslimit = 10000000
        world = evm.EVMWorld(
            constraints,
            blocknumber=blocknumber,
            timestamp=timestamp,
            difficulty=difficulty,
            coinbase=coinbase,
            gaslimit=gaslimit,
        )

        acc_addr = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        acc_code = unhexlify(
            "6001600181810181810181810181810181810181810181810181810181810181810181810181810181810181810181810181810181810160005260206000f3"
        )
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F2947DEF4CF144679DA39C4C32BDC35681
        price = 0x5AF3107A4000
        value = 1000000000000000000
        gas = 1000000
        data = ""
        # open a fake tx, no funds send
        world._open_transaction("CALL", address, price, data, caller, value, gas=gas)

        # This variable might seem redundant in some tests - don't forget it is auto generated
        # and there are cases in which we need it ;)
        result, returndata = self._test_run(world)

        # World sanity checks - those should not change, right?
        self.assertEqual(solve(world.block_number()), 0)
        self.assertEqual(solve(world.block_gaslimit()), 10000000)
        self.assertEqual(solve(world.block_timestamp()), 1)
        self.assertEqual(solve(world.block_difficulty()), 256)
        self.assertEqual(solve(world.block_coinbase()), 0x2ADC25665018AA1FE0E6BC666DAC8FC2697FF9BA)

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 0)
        self.assertEqual(
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 1000000000000000000
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6),
            unhexlify(
                "6001600181810181810181810181810181810181810181810181810181810181810181810181810181810181810181810181810181810160005260206000f3"
            ),
        )
        # check outs
        self.assertEqual(
            returndata,
            unhexlify("0000000000000000000000000000000000000000000000000000000000001055"),
        )
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
        self.assertEqual(solve(world.current_vm.gas), 999826)

    def test_expPowerOf256Of256_14(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: expPowerOf256Of256_14.json
        sha256sum: 771926f9010806c01969e395afd82b9dc72e0436d9c229a055ab772d5bee6ca7
        Code:     PUSH1 0xe
                  PUSH2 0x100
                  EXP
                  PUSH2 0x100
                  EXP
                  PUSH1 0x0
                  SSTORE
                  PUSH1 0xe
                  PUSH1 0xff
                  EXP
                  PUSH2 0x100
                  EXP
                  PUSH1 0x1
                  SSTORE
                  PUSH1 0xe
                  PUSH2 0x101
                  EXP
                  PUSH2 0x100
                  EXP
                  PUSH1 0x2
                  SSTORE
                  PUSH1 0xe
                  PUSH2 0x100
                  EXP
                  PUSH1 0xff
                  EXP
                  PUSH1 0x3
                  SSTORE
                  PUSH1 0xe
                  PUSH1 0xff
                  EXP
                  PUSH1 0xff
                  EXP
                  PUSH1 0x4
                  SSTORE
                  PUSH1 0xe
                  PUSH2 0x101
                  EXP
                  PUSH1 0xff
                  EXP
                  PUSH1 0x5
                  SSTORE
                  PUSH1 0xe
                  PUSH2 0x100
                  EXP
                  PUSH2 0x101
                  EXP
                  PUSH1 0x6
                  SSTORE
                  PUSH1 0xe
                  PUSH1 0xff
                  EXP
                  PUSH2 0x101
                  EXP
                  PUSH1 0x7
                  SSTORE
                  PUSH1 0xe
                  PUSH2 0x101
                  EXP
                  PUSH2 0x101
                  EXP
                  PUSH1 0x8
                  SSTORE
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
        gaslimit = 10000000
        world = evm.EVMWorld(
            constraints,
            blocknumber=blocknumber,
            timestamp=timestamp,
            difficulty=difficulty,
            coinbase=coinbase,
            gaslimit=gaslimit,
        )

        acc_addr = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        acc_code = unhexlify(
            "600e6101000a6101000a600055600e60ff0a6101000a600155600e6101010a6101000a600255600e6101000a60ff0a600355600e60ff0a60ff0a600455600e6101010a60ff0a600555600e6101000a6101010a600655600e60ff0a6101010a600755600e6101010a6101010a600855"
        )
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F2947DEF4CF144679DA39C4C32BDC35681
        price = 0x5AF3107A4000
        value = 1000000000000000000
        gas = 1000000
        data = ""
        # open a fake tx, no funds send
        world._open_transaction("CALL", address, price, data, caller, value, gas=gas)

        # This variable might seem redundant in some tests - don't forget it is auto generated
        # and there are cases in which we need it ;)
        result, returndata = self._test_run(world)

        # World sanity checks - those should not change, right?
        self.assertEqual(solve(world.block_number()), 0)
        self.assertEqual(solve(world.block_gaslimit()), 10000000)
        self.assertEqual(solve(world.block_timestamp()), 1)
        self.assertEqual(solve(world.block_difficulty()), 256)
        self.assertEqual(solve(world.block_coinbase()), 0x2ADC25665018AA1FE0E6BC666DAC8FC2697FF9BA)

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 0)
        self.assertEqual(
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 1000000000000000000
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6),
            unhexlify(
                "600e6101000a6101000a600055600e60ff0a6101000a600155600e6101010a6101000a600255600e6101000a60ff0a600355600e60ff0a60ff0a600455600e6101010a60ff0a600555600e6101000a6101010a600655600e60ff0a6101010a600755600e6101010a6101010a600855"
            ),
        )
        # check storage
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x03)),
            0xDB9902EC698218879EC55C33085514FF7F000000000000000000000000000001,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x04)),
            0x83FAB06C6C8FEF761EBBB9534C06AC2A9D61820623008069062FF3B1E1F200FF,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x05)),
            0x3F791DD183ED5B963BD86E0DBA1A9DD5B8CEEB078F15C73062F1942FD40E00FF,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x06)),
            0xE0BFA28FC9B0F000B68FB921F7AA6AFF81000000000000000000000000000001,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x07)),
            0x8133B760DFAE27560EB490F235DDFA301F058DEE4F01F3FE4B3567D0D3F20101,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x08)),
            0xCD4CD0124E983AF71620FB5F98275965C6A8BEBC4B8ADC288B63224EE20E0101,
        )
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
        self.assertEqual(solve(world.current_vm.gas), 863302)

    def test_add4(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: add4.json
        sha256sum: ca8e6b511dceca6765685b6b80463fceadd6b15ee71c9694390828a72a884a1d
        Code:     PUSH32 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
                  PUSH1 0x1
                  ADD
                  PUSH1 0x0
                  SSTORE
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
        acc_code = unhexlify(
            "7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff600101600055"
        )
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F2947DEF4CF144679DA39C4C32BDC35681
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

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 0)
        self.assertEqual(
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 1000000000000000000
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6),
            unhexlify(
                "7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff600101600055"
            ),
        )
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
        self.assertEqual(solve(world.current_vm.gas), 94988)

    def test_expPowerOf256Of256_0(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: expPowerOf256Of256_0.json
        sha256sum: 90140ff94b6bfacb841fe9ec94969da8c2ff50d4a298e567ab9e2bc3924684cd
        Code:     PUSH1 0x0
                  PUSH2 0x100
                  EXP
                  PUSH2 0x100
                  EXP
                  PUSH1 0x0
                  SSTORE
                  PUSH1 0x0
                  PUSH1 0xff
                  EXP
                  PUSH2 0x100
                  EXP
                  PUSH1 0x1
                  SSTORE
                  PUSH1 0x0
                  PUSH2 0x101
                  EXP
                  PUSH2 0x100
                  EXP
                  PUSH1 0x2
                  SSTORE
                  PUSH1 0x0
                  PUSH2 0x100
                  EXP
                  PUSH1 0xff
                  EXP
                  PUSH1 0x3
                  SSTORE
                  PUSH1 0x0
                  PUSH1 0xff
                  EXP
                  PUSH1 0xff
                  EXP
                  PUSH1 0x4
                  SSTORE
                  PUSH1 0x0
                  PUSH2 0x101
                  EXP
                  PUSH1 0xff
                  EXP
                  PUSH1 0x5
                  SSTORE
                  PUSH1 0x0
                  PUSH2 0x100
                  EXP
                  PUSH2 0x101
                  EXP
                  PUSH1 0x6
                  SSTORE
                  PUSH1 0x0
                  PUSH1 0xff
                  EXP
                  PUSH2 0x101
                  EXP
                  PUSH1 0x7
                  SSTORE
                  PUSH1 0x0
                  PUSH2 0x101
                  EXP
                  PUSH2 0x101
                  EXP
                  PUSH1 0x8
                  SSTORE
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
        gaslimit = 10000000
        world = evm.EVMWorld(
            constraints,
            blocknumber=blocknumber,
            timestamp=timestamp,
            difficulty=difficulty,
            coinbase=coinbase,
            gaslimit=gaslimit,
        )

        acc_addr = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        acc_code = unhexlify(
            "60006101000a6101000a600055600060ff0a6101000a60015560006101010a6101000a60025560006101000a60ff0a600355600060ff0a60ff0a60045560006101010a60ff0a60055560006101000a6101010a600655600060ff0a6101010a60075560006101010a6101010a600855"
        )
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F2947DEF4CF144679DA39C4C32BDC35681
        price = 0x5AF3107A4000
        value = 1000000000000000000
        gas = 1000000
        data = ""
        # open a fake tx, no funds send
        world._open_transaction("CALL", address, price, data, caller, value, gas=gas)

        # This variable might seem redundant in some tests - don't forget it is auto generated
        # and there are cases in which we need it ;)
        result, returndata = self._test_run(world)

        # World sanity checks - those should not change, right?
        self.assertEqual(solve(world.block_number()), 0)
        self.assertEqual(solve(world.block_gaslimit()), 10000000)
        self.assertEqual(solve(world.block_timestamp()), 1)
        self.assertEqual(solve(world.block_difficulty()), 256)
        self.assertEqual(solve(world.block_coinbase()), 0x2ADC25665018AA1FE0E6BC666DAC8FC2697FF9BA)

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 0)
        self.assertEqual(
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 1000000000000000000
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6),
            unhexlify(
                "60006101000a6101000a600055600060ff0a6101000a60015560006101010a6101000a60025560006101000a60ff0a600355600060ff0a60ff0a60045560006101010a60ff0a60055560006101000a6101010a600655600060ff0a6101010a60075560006101010a6101010a600855"
            ),
        )
        # check storage
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x00)), 0x0100
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x01)), 0x0100
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x02)), 0x0100
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x03)), 0xFF
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x04)), 0xFF
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x05)), 0xFF
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x06)), 0x0101
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x07)), 0x0101
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x08)), 0x0101
        )
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
        self.assertEqual(solve(world.current_vm.gas), 819622)

    def test_expPowerOf256_13(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: expPowerOf256_13.json
        sha256sum: 7175a5c1d4422f0a80afaf7e92eff51584e1529057d43a7cc177cc4cc6ddb491
        Code:     PUSH1 0xd
                  PUSH2 0x100
                  EXP
                  PUSH1 0x0
                  SSTORE
                  PUSH1 0xd
                  PUSH1 0xff
                  EXP
                  PUSH1 0x1
                  SSTORE
                  PUSH1 0xd
                  PUSH2 0x101
                  EXP
                  PUSH1 0x2
                  SSTORE
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
        acc_code = unhexlify("600d6101000a600055600d60ff0a600155600d6101010a600255")
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F2947DEF4CF144679DA39C4C32BDC35681
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

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 0)
        self.assertEqual(
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 1000000000000000000
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6),
            unhexlify("600d6101000a600055600d60ff0a600155600d6101010a600255"),
        )
        # check storage
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x00)),
            0x0100000000000000000000000000,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x01)),
            0xF34CE4C5FFAD5104361DB20CFF,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x02)),
            0x010D4F20D00DBAB909CC1E4E0D01,
        )
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
        self.assertEqual(solve(world.current_vm.gas), 39913)

    def test_sdiv0(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: sdiv0.json
        sha256sum: f247d5d6906019548216c29459efebace369512d19df0e266ecc8a2028dc1960
        Code:     PUSH32 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
                  PUSH32 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
                  PUSH1 0x0
                  SUB
                  SDIV
                  PUSH1 0x0
                  SSTORE
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
        acc_code = unhexlify(
            "7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff60000305600055"
        )
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F2947DEF4CF144679DA39C4C32BDC35681
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

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 0)
        self.assertEqual(
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 1000000000000000000
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6),
            unhexlify(
                "7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff60000305600055"
            ),
        )
        # check storage
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x00)),
            0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF,
        )
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
        self.assertEqual(solve(world.current_vm.gas), 79980)

    def test_expPowerOf256Of256_24(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: expPowerOf256Of256_24.json
        sha256sum: a6e5372e634098106ecb26b9450645cf2f57b9cf067a90f3863dc9ab21d88b50
        Code:     PUSH1 0x18
                  PUSH2 0x100
                  EXP
                  PUSH2 0x100
                  EXP
                  PUSH1 0x0
                  SSTORE
                  PUSH1 0x18
                  PUSH1 0xff
                  EXP
                  PUSH2 0x100
                  EXP
                  PUSH1 0x1
                  SSTORE
                  PUSH1 0x18
                  PUSH2 0x101
                  EXP
                  PUSH2 0x100
                  EXP
                  PUSH1 0x2
                  SSTORE
                  PUSH1 0x18
                  PUSH2 0x100
                  EXP
                  PUSH1 0xff
                  EXP
                  PUSH1 0x3
                  SSTORE
                  PUSH1 0x18
                  PUSH1 0xff
                  EXP
                  PUSH1 0xff
                  EXP
                  PUSH1 0x4
                  SSTORE
                  PUSH1 0x18
                  PUSH2 0x101
                  EXP
                  PUSH1 0xff
                  EXP
                  PUSH1 0x5
                  SSTORE
                  PUSH1 0x18
                  PUSH2 0x100
                  EXP
                  PUSH2 0x101
                  EXP
                  PUSH1 0x6
                  SSTORE
                  PUSH1 0x18
                  PUSH1 0xff
                  EXP
                  PUSH2 0x101
                  EXP
                  PUSH1 0x7
                  SSTORE
                  PUSH1 0x18
                  PUSH2 0x101
                  EXP
                  PUSH2 0x101
                  EXP
                  PUSH1 0x8
                  SSTORE
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
        gaslimit = 10000000
        world = evm.EVMWorld(
            constraints,
            blocknumber=blocknumber,
            timestamp=timestamp,
            difficulty=difficulty,
            coinbase=coinbase,
            gaslimit=gaslimit,
        )

        acc_addr = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        acc_code = unhexlify(
            "60186101000a6101000a600055601860ff0a6101000a60015560186101010a6101000a60025560186101000a60ff0a600355601860ff0a60ff0a60045560186101010a60ff0a60055560186101000a6101010a600655601860ff0a6101010a60075560186101010a6101010a600855"
        )
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F2947DEF4CF144679DA39C4C32BDC35681
        price = 0x5AF3107A4000
        value = 1000000000000000000
        gas = 1000000
        data = ""
        # open a fake tx, no funds send
        world._open_transaction("CALL", address, price, data, caller, value, gas=gas)

        # This variable might seem redundant in some tests - don't forget it is auto generated
        # and there are cases in which we need it ;)
        result, returndata = self._test_run(world)

        # World sanity checks - those should not change, right?
        self.assertEqual(solve(world.block_number()), 0)
        self.assertEqual(solve(world.block_gaslimit()), 10000000)
        self.assertEqual(solve(world.block_timestamp()), 1)
        self.assertEqual(solve(world.block_difficulty()), 256)
        self.assertEqual(solve(world.block_coinbase()), 0x2ADC25665018AA1FE0E6BC666DAC8FC2697FF9BA)

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 0)
        self.assertEqual(
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 1000000000000000000
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6),
            unhexlify(
                "60186101000a6101000a600055601860ff0a6101000a60015560186101010a6101000a60025560186101000a60ff0a600355601860ff0a60ff0a60045560186101010a60ff0a60055560186101000a6101010a600655601860ff0a6101010a60075560186101010a6101010a600855"
            ),
        )
        # check storage
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x03)),
            0x5C33085514FF7F00000000000000000000000000000000000000000000000001,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x04)),
            0xD542E526003539EAD104274AFF2D78332366E29D328C2161F0C120731FE800FF,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x05)),
            0xC706CB25E8384CE9BB5C9CB48415238BA03E16C448E292C0A101843B081800FF,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x06)),
            0xB921F7AA6AFF8100000000000000000000000000000000000000000000000001,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x07)),
            0x4CA55F89202C524CB0F1CB3195D13C8D94A9F7A05C59E1D4031577C707E80101,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x08)),
            0x8C4B0574E9156B80035F3ECDCF1FE79D273ED7559747A4322BCD338F20180101,
        )
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
        self.assertEqual(solve(world.current_vm.gas), 862402)

    def test_expPowerOf256_30(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: expPowerOf256_30.json
        sha256sum: 40b900a85b4a54fda4efc8e6bcdbf7ba6b7535de4223a3479188966314336500
        Code:     PUSH1 0x1e
                  PUSH2 0x100
                  EXP
                  PUSH1 0x0
                  SSTORE
                  PUSH1 0x1e
                  PUSH1 0xff
                  EXP
                  PUSH1 0x1
                  SSTORE
                  PUSH1 0x1e
                  PUSH2 0x101
                  EXP
                  PUSH1 0x2
                  SSTORE
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
        acc_code = unhexlify("601e6101000a600055601e60ff0a600155601e6101010a600255")
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F2947DEF4CF144679DA39C4C32BDC35681
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

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 0)
        self.assertEqual(
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 1000000000000000000
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6),
            unhexlify("601e6101000a600055601e60ff0a600155601e6101010a600255"),
        )
        # check storage
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x00)),
            0x01000000000000000000000000000000000000000000000000000000000000,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x01)),
            0xE3A38CE946B71E74E8EBC966D90F0B139E66B560E1F5B542C0FD25B2E201,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x02)),
            0x011FC34942D8D9831A0811D8412AECF1E1F58031FFBC16699C151CDDB31E01,
        )
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
        self.assertEqual(solve(world.current_vm.gas), 39913)

    def test_expXY(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: expXY.json
        sha256sum: 946461d4eabea507c8507010fd972cc8a0bc845d05865cf9eabbb5e93b7a169a
        Code:     PUSH1 0x0
                  CALLDATALOAD
                  PUSH1 0x0
                  SSTORE
                  PUSH1 0x20
                  CALLDATALOAD
                  PUSH1 0x1
                  SSTORE
                  PUSH1 0x1
                  SLOAD
                  PUSH1 0x0
                  SLOAD
                  EXP
                  PUSH1 0x2
                  SSTORE
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
        acc_code = unhexlify("6000356000556020356001556001546000540a600255")
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F2947DEF4CF144679DA39C4C32BDC35681
        price = 0x5AF3107A4000
        value = 1000000000000000000
        gas = 100000
        data = b"\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x02\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x01\x00\x00\x00\x00\x00\x0f"
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

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 0)
        self.assertEqual(
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 1000000000000000000
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6),
            unhexlify("6000356000556020356001556001546000540a600255"),
        )
        # check storage
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x00)), 0x02
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x01)),
            0x0100000000000F,
        )
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
        self.assertEqual(solve(world.current_vm.gas), 54793)

    def test_addmod2_0(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: addmod2_0.json
        sha256sum: bbf4dffad9e7377fa52c268f04c35b73067d116100ee6e3e063af74e5114c8a0
        Code:     PUSH1 0x3
                  PUSH1 0x1
                  PUSH1 0x6
                  PUSH1 0x0
                  SUB
                  ADDMOD
                  PUSH1 0x3
                  PUSH1 0x5
                  PUSH1 0x0
                  SUB
                  SMOD
                  EQ
                  PUSH1 0x0
                  SSTORE
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
        acc_code = unhexlify("60036001600660000308600360056000030714600055")
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F2947DEF4CF144679DA39C4C32BDC35681
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

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 0)
        self.assertEqual(
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 1000000000000000000
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6),
            unhexlify("60036001600660000308600360056000030714600055"),
        )
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
        self.assertEqual(solve(world.current_vm.gas), 94954)

    def test_sdiv3(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: sdiv3.json
        sha256sum: 0d4372b97497489fdb38dc01e5b03d73e20d29b57d638564d6e54d87c4dbd46f
        Code:     PUSH1 0x2
                  PUSH1 0x0
                  SUB
                  PUSH1 0x4
                  SDIV
                  PUSH1 0x0
                  SSTORE
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
        acc_code = unhexlify("6002600003600405600055")
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F2947DEF4CF144679DA39C4C32BDC35681
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

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 0)
        self.assertEqual(
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 1000000000000000000
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6),
            unhexlify("6002600003600405600055"),
        )
        # check storage
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x00)),
            0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFE,
        )
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
        self.assertEqual(solve(world.current_vm.gas), 79980)

    def test_expPowerOf256Of256_7(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: expPowerOf256Of256_7.json
        sha256sum: b138bd8537c0d2aeab0e2b0ef55017e320bfc2fd2102d283e38a983bd30bd064
        Code:     PUSH1 0x7
                  PUSH2 0x100
                  EXP
                  PUSH2 0x100
                  EXP
                  PUSH1 0x0
                  SSTORE
                  PUSH1 0x7
                  PUSH1 0xff
                  EXP
                  PUSH2 0x100
                  EXP
                  PUSH1 0x1
                  SSTORE
                  PUSH1 0x7
                  PUSH2 0x101
                  EXP
                  PUSH2 0x100
                  EXP
                  PUSH1 0x2
                  SSTORE
                  PUSH1 0x7
                  PUSH2 0x100
                  EXP
                  PUSH1 0xff
                  EXP
                  PUSH1 0x3
                  SSTORE
                  PUSH1 0x7
                  PUSH1 0xff
                  EXP
                  PUSH1 0xff
                  EXP
                  PUSH1 0x4
                  SSTORE
                  PUSH1 0x7
                  PUSH2 0x101
                  EXP
                  PUSH1 0xff
                  EXP
                  PUSH1 0x5
                  SSTORE
                  PUSH1 0x7
                  PUSH2 0x100
                  EXP
                  PUSH2 0x101
                  EXP
                  PUSH1 0x6
                  SSTORE
                  PUSH1 0x7
                  PUSH1 0xff
                  EXP
                  PUSH2 0x101
                  EXP
                  PUSH1 0x7
                  SSTORE
                  PUSH1 0x7
                  PUSH2 0x101
                  EXP
                  PUSH2 0x101
                  EXP
                  PUSH1 0x8
                  SSTORE
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
        gaslimit = 10000000
        world = evm.EVMWorld(
            constraints,
            blocknumber=blocknumber,
            timestamp=timestamp,
            difficulty=difficulty,
            coinbase=coinbase,
            gaslimit=gaslimit,
        )

        acc_addr = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        acc_code = unhexlify(
            "60076101000a6101000a600055600760ff0a6101000a60015560076101010a6101000a60025560076101000a60ff0a600355600760ff0a60ff0a60045560076101010a60ff0a60055560076101000a6101010a600655600760ff0a6101010a60075560076101010a6101010a600855"
        )
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F2947DEF4CF144679DA39C4C32BDC35681
        price = 0x5AF3107A4000
        value = 1000000000000000000
        gas = 1000000
        data = ""
        # open a fake tx, no funds send
        world._open_transaction("CALL", address, price, data, caller, value, gas=gas)

        # This variable might seem redundant in some tests - don't forget it is auto generated
        # and there are cases in which we need it ;)
        result, returndata = self._test_run(world)

        # World sanity checks - those should not change, right?
        self.assertEqual(solve(world.block_number()), 0)
        self.assertEqual(solve(world.block_gaslimit()), 10000000)
        self.assertEqual(solve(world.block_timestamp()), 1)
        self.assertEqual(solve(world.block_difficulty()), 256)
        self.assertEqual(solve(world.block_coinbase()), 0x2ADC25665018AA1FE0E6BC666DAC8FC2697FF9BA)

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 0)
        self.assertEqual(
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 1000000000000000000
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6),
            unhexlify(
                "60076101000a6101000a600055600760ff0a6101000a60015560076101010a6101000a60025560076101000a60ff0a600355600760ff0a60ff0a60045560076101010a60ff0a60055560076101000a6101010a600655600760ff0a6101010a60075560076101010a6101010a600855"
            ),
        )
        # check storage
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x03)),
            0x8BB02654111AD8C60AD8AF132283A81F455C33085514FF7F0000000000000001,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x04)),
            0xA8F75C129DBB8466D6703A2A0B8212131B3248D70E2478862AC40FE17485FEFF,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x05)),
            0x5FD4D2DE580383EE59F5E800DDB3F1717CEAE03AEDE19D3DEC5E5A69918700FF,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x06)),
            0xC8624230B524B85D6340DA48A5DB20370FB921F7AA6AFF810000000000000001,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x07)),
            0x287B58A5A13CD7F454468CA616C181712F5ED25433A7D5A894B6CED35F87FF01,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x08)),
            0x09930D11AC2804FA977BF951593C8DFF8498779CC0CDC5812A4FBA2F98870101,
        )
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
        self.assertEqual(solve(world.current_vm.gas), 863932)

    def test_addmodDivByZero3(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: addmodDivByZero3.json
        sha256sum: c66eaa3ef9cc720a3194d2e4031d7f285eabb2f529931057fcaa06efbf4b8453
        Code:     PUSH1 0x1
                  PUSH1 0x0
                  PUSH1 0x0
                  PUSH1 0x0
                  ADDMOD
                  SUB
                  PUSH1 0x0
                  SSTORE
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
        acc_code = unhexlify("60016000600060000803600055")
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F2947DEF4CF144679DA39C4C32BDC35681
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

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 0)
        self.assertEqual(
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 1000000000000000000
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6),
            unhexlify("60016000600060000803600055"),
        )
        # check storage
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x00)),
            0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF,
        )
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
        self.assertEqual(solve(world.current_vm.gas), 79974)

    def test_sub0(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: sub0.json
        sha256sum: e185a37296e08e7dec9a4f77e22663970f19de5a3c25fb0061df02a0743b1d05
        Code:     PUSH1 0x1
                  PUSH1 0x17
                  SUB
                  PUSH1 0x0
                  SSTORE
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
        acc_code = unhexlify("6001601703600055")
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F2947DEF4CF144679DA39C4C32BDC35681
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

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 0)
        self.assertEqual(
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 1000000000000000000
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6), unhexlify("6001601703600055")
        )
        # check storage
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x00)), 0x16
        )
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
        self.assertEqual(solve(world.current_vm.gas), 79988)

    def test_expPowerOf256Of256_27(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: expPowerOf256Of256_27.json
        sha256sum: a1d19ca0171c8b91922a91db49e2f3faadd95be335783b97f016247f240224c0
        Code:     PUSH1 0x1b
                  PUSH2 0x100
                  EXP
                  PUSH2 0x100
                  EXP
                  PUSH1 0x0
                  SSTORE
                  PUSH1 0x1b
                  PUSH1 0xff
                  EXP
                  PUSH2 0x100
                  EXP
                  PUSH1 0x1
                  SSTORE
                  PUSH1 0x1b
                  PUSH2 0x101
                  EXP
                  PUSH2 0x100
                  EXP
                  PUSH1 0x2
                  SSTORE
                  PUSH1 0x1b
                  PUSH2 0x100
                  EXP
                  PUSH1 0xff
                  EXP
                  PUSH1 0x3
                  SSTORE
                  PUSH1 0x1b
                  PUSH1 0xff
                  EXP
                  PUSH1 0xff
                  EXP
                  PUSH1 0x4
                  SSTORE
                  PUSH1 0x1b
                  PUSH2 0x101
                  EXP
                  PUSH1 0xff
                  EXP
                  PUSH1 0x5
                  SSTORE
                  PUSH1 0x1b
                  PUSH2 0x100
                  EXP
                  PUSH2 0x101
                  EXP
                  PUSH1 0x6
                  SSTORE
                  PUSH1 0x1b
                  PUSH1 0xff
                  EXP
                  PUSH2 0x101
                  EXP
                  PUSH1 0x7
                  SSTORE
                  PUSH1 0x1b
                  PUSH2 0x101
                  EXP
                  PUSH2 0x101
                  EXP
                  PUSH1 0x8
                  SSTORE
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
        gaslimit = 10000000
        world = evm.EVMWorld(
            constraints,
            blocknumber=blocknumber,
            timestamp=timestamp,
            difficulty=difficulty,
            coinbase=coinbase,
            gaslimit=gaslimit,
        )

        acc_addr = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        acc_code = unhexlify(
            "601b6101000a6101000a600055601b60ff0a6101000a600155601b6101010a6101000a600255601b6101000a60ff0a600355601b60ff0a60ff0a600455601b6101010a60ff0a600555601b6101000a6101010a600655601b60ff0a6101010a600755601b6101010a6101010a600855"
        )
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F2947DEF4CF144679DA39C4C32BDC35681
        price = 0x5AF3107A4000
        value = 1000000000000000000
        gas = 1000000
        data = ""
        # open a fake tx, no funds send
        world._open_transaction("CALL", address, price, data, caller, value, gas=gas)

        # This variable might seem redundant in some tests - don't forget it is auto generated
        # and there are cases in which we need it ;)
        result, returndata = self._test_run(world)

        # World sanity checks - those should not change, right?
        self.assertEqual(solve(world.block_number()), 0)
        self.assertEqual(solve(world.block_gaslimit()), 10000000)
        self.assertEqual(solve(world.block_timestamp()), 1)
        self.assertEqual(solve(world.block_difficulty()), 256)
        self.assertEqual(solve(world.block_coinbase()), 0x2ADC25665018AA1FE0E6BC666DAC8FC2697FF9BA)

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 0)
        self.assertEqual(
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 1000000000000000000
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6),
            unhexlify(
                "601b6101000a6101000a600055601b60ff0a6101000a600155601b6101010a6101000a600255601b6101000a60ff0a600355601b60ff0a60ff0a600455601b6101010a60ff0a600555601b6101000a6101010a600655601b60ff0a6101010a600755601b6101010a6101010a600855"
            ),
        )
        # check storage
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x03)),
            0x5514FF7F00000000000000000000000000000000000000000000000000000001,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x04)),
            0x178918FFBCB401D4EFD2F7DFB4D01A897172267F0F491121AC52DD614899FEFF,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x05)),
            0x38ECFF71480CA0B422F2ED6F780D5FEAD2AE234A49104B10A86F7F0DD19B00FF,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x06)),
            0xAA6AFF8100000000000000000000000000000000000000000000000000000001,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x07)),
            0xD02811CB5DC1D80567E810532B235B7672F5C78CD6E89BB511D5E2D8F79BFF01,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x08)),
            0x1B4E6404F474C18055D30BB8987672F59E97980D6F9DE1764C0FBEC5EC9B0101,
        )
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
        self.assertEqual(solve(world.current_vm.gas), 862132)

    def test_divByZero(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: divByZero.json
        sha256sum: 3c90b75a836a6d2f79054eb6bb179afa94045229bbf98f4f0ef6603d353cc7bd
        Code:     PUSH1 0x0
                  PUSH1 0x2
                  DIV
                  PUSH1 0x0
                  SSTORE
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
        acc_code = unhexlify("6000600204600055")
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F2947DEF4CF144679DA39C4C32BDC35681
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

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 0)
        self.assertEqual(
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 1000000000000000000
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6), unhexlify("6000600204600055")
        )
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
        self.assertEqual(solve(world.current_vm.gas), 94986)

    def test_expPowerOf256_25(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: expPowerOf256_25.json
        sha256sum: 55f40ba018ea3e5a3c2a3033c1261e54e2ff042f2d3c9561fffecdf650f081c0
        Code:     PUSH1 0x19
                  PUSH2 0x100
                  EXP
                  PUSH1 0x0
                  SSTORE
                  PUSH1 0x19
                  PUSH1 0xff
                  EXP
                  PUSH1 0x1
                  SSTORE
                  PUSH1 0x19
                  PUSH2 0x101
                  EXP
                  PUSH1 0x2
                  SSTORE
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
        acc_code = unhexlify("60196101000a600055601960ff0a60015560196101010a600255")
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F2947DEF4CF144679DA39C4C32BDC35681
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

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 0)
        self.assertEqual(
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 1000000000000000000
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6),
            unhexlify("60196101000a600055601960ff0a60015560196101010a600255"),
        )
        # check storage
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x00)),
            0x0100000000000000000000000000000000000000000000000000,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x01)),
            0xE823349D2286A5EC3DE3529625F683E56C0903589EFAD418FF,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x02)),
            0x011A352E3C45325C4583EB6149E1B7D4E73F709BBB72FD2C1901,
        )
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
        self.assertEqual(solve(world.current_vm.gas), 39913)

    def test_sub3(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: sub3.json
        sha256sum: 51d9d78dc7c91e221762a0d94914b0a98599d2e52fe6751aa69852ff4b7e5736
        Code:     PUSH32 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
                  PUSH1 0x0
                  SUB
                  PUSH1 0x0
                  SSTORE
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
        acc_code = unhexlify(
            "7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff600003600055"
        )
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F2947DEF4CF144679DA39C4C32BDC35681
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

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 0)
        self.assertEqual(
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 1000000000000000000
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6),
            unhexlify(
                "7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff600003600055"
            ),
        )
        # check storage
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x00)), 0x01
        )
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
        self.assertEqual(solve(world.current_vm.gas), 79988)

    def test_sdivByZero1(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: sdivByZero1.json
        sha256sum: 9a2207240279ed9e305737bf728c43c2b7d3bb0f40e738b88c88cad1ba8dcc63
        Code:     PUSH1 0x0
                  PUSH32 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
                  PUSH1 0x0
                  SUB
                  SDIV
                  PUSH1 0x0
                  SSTORE
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
        acc_code = unhexlify(
            "60007fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff60000305600055"
        )
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F2947DEF4CF144679DA39C4C32BDC35681
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

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 0)
        self.assertEqual(
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 1000000000000000000
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6),
            unhexlify(
                "60007fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff60000305600055"
            ),
        )
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
        self.assertEqual(solve(world.current_vm.gas), 94980)

    def test_divByNonZero2(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: divByNonZero2.json
        sha256sum: e0063bfc165977cec03383edad0916adad5c509bfbae2d0ed1b3ee73e703e047
        Code:     PUSH1 0x18
                  PUSH1 0x0
                  DIV
                  PUSH1 0x0
                  SSTORE
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
        acc_code = unhexlify("6018600004600055")
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F2947DEF4CF144679DA39C4C32BDC35681
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

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 0)
        self.assertEqual(
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 1000000000000000000
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6), unhexlify("6018600004600055")
        )
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
        self.assertEqual(solve(world.current_vm.gas), 94986)

    def test_signextend_Overflow_dj42(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: signextend_Overflow_dj42.json
        sha256sum: 98eb87e0704d92cf48dd7c2124eb1e7c80e36955cd08cbd295d86565878a512a
        Code:     PUSH1 0x5
                  JUMP
                  JUMPDEST
                  STOP
                  JUMPDEST
                  PUSH2 0x8000
                  DUP1
                  PUSH9 0x10000000000000001
                  SIGNEXTEND
                  PUSH2 0x8001
                  GT
                  PUSH1 0x3
                  JUMPI
                  PUSH4 0xbadf000d
                  PUSH1 0x11
                  SSTORE
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
        gaslimit = 10000000
        world = evm.EVMWorld(
            constraints,
            blocknumber=blocknumber,
            timestamp=timestamp,
            difficulty=difficulty,
            coinbase=coinbase,
            gaslimit=gaslimit,
        )

        acc_addr = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        acc_code = unhexlify(
            "6005565b005b61800080680100000000000000010b6180011160035763badf000d601155"
        )
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F2947DEF4CF144679DA39C4C32BDC35681
        price = 0x5AF3107A4000
        value = 1000000000000000000
        gas = 1000000
        data = ""
        # open a fake tx, no funds send
        world._open_transaction("CALL", address, price, data, caller, value, gas=gas)

        # This variable might seem redundant in some tests - don't forget it is auto generated
        # and there are cases in which we need it ;)
        result, returndata = self._test_run(world)

        # World sanity checks - those should not change, right?
        self.assertEqual(solve(world.block_number()), 0)
        self.assertEqual(solve(world.block_gaslimit()), 10000000)
        self.assertEqual(solve(world.block_timestamp()), 1)
        self.assertEqual(solve(world.block_difficulty()), 256)
        self.assertEqual(solve(world.block_coinbase()), 0x2ADC25665018AA1FE0E6BC666DAC8FC2697FF9BA)

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 0)
        self.assertEqual(
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 1000000000000000000
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6),
            unhexlify("6005565b005b61800080680100000000000000010b6180011160035763badf000d601155"),
        )
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
        self.assertEqual(solve(world.current_vm.gas), 999954)

    def test_expPowerOf256_28(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: expPowerOf256_28.json
        sha256sum: 1a20d105592e063cd1a2736383aba235513940ea6a3e91fea29aa0db06e1f88f
        Code:     PUSH1 0x1c
                  PUSH2 0x100
                  EXP
                  PUSH1 0x0
                  SSTORE
                  PUSH1 0x1c
                  PUSH1 0xff
                  EXP
                  PUSH1 0x1
                  SSTORE
                  PUSH1 0x1c
                  PUSH2 0x101
                  EXP
                  PUSH1 0x2
                  SSTORE
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
        acc_code = unhexlify("601c6101000a600055601c60ff0a600155601c6101010a600255")
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F2947DEF4CF144679DA39C4C32BDC35681
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

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 0)
        self.assertEqual(
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 1000000000000000000
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6),
            unhexlify("601c6101000a600055601c60ff0a600155601c6101010a600255"),
        )
        # check storage
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x00)),
            0x0100000000000000000000000000000000000000000000000000000000,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x01)),
            0xE56D8280C5C1DC6BE448760A77F47C1750F146FD962467EE3579E401,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x02)),
            0x011D871D80B9E4FF369BA3F4B3CE9BEB6F2BB9931FE9243807CD7A1C01,
        )
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
        self.assertEqual(solve(world.current_vm.gas), 39913)

    def test_addmod2(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: addmod2.json
        sha256sum: 1bfa788fb8650cbb35277be2e9d56d4ef9de41e10773020c16a6589b3c7479a6
        Code:     PUSH1 0x3
                  PUSH1 0x1
                  PUSH1 0x6
                  PUSH1 0x0
                  SUB
                  ADDMOD
                  PUSH1 0x0
                  SSTORE
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
        acc_code = unhexlify("60036001600660000308600055")
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F2947DEF4CF144679DA39C4C32BDC35681
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

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 0)
        self.assertEqual(
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 1000000000000000000
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6),
            unhexlify("60036001600660000308600055"),
        )
        # check storage
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x00)), 0x02
        )
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
        self.assertEqual(solve(world.current_vm.gas), 79974)

    def test_mulmod3(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: mulmod3.json
        sha256sum: 0251e3f2116b47183a5c072b9b2194a133ed124ec402ec38e9b804e6372b293b
        Code:     PUSH1 0x3
                  PUSH1 0x0
                  SUB
                  PUSH1 0x1
                  PUSH1 0x5
                  MULMOD
                  PUSH1 0x0
                  SSTORE
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
        acc_code = unhexlify("60036000036001600509600055")
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F2947DEF4CF144679DA39C4C32BDC35681
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

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 0)
        self.assertEqual(
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 1000000000000000000
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6),
            unhexlify("60036000036001600509600055"),
        )
        # check storage
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x00)), 0x05
        )
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
        self.assertEqual(solve(world.current_vm.gas), 79974)

    def test_sub2(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: sub2.json
        sha256sum: 6df63508965f32e5b145e711c7a7d5a0226182745ad7ced9596d22e869d4ce26
        Code:     PUSH1 0x17
                  PUSH1 0x0
                  SUB
                  PUSH1 0x0
                  SSTORE
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
        acc_code = unhexlify("6017600003600055")
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F2947DEF4CF144679DA39C4C32BDC35681
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

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 0)
        self.assertEqual(
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 1000000000000000000
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6), unhexlify("6017600003600055")
        )
        # check storage
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x00)),
            0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFE9,
        )
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
        self.assertEqual(solve(world.current_vm.gas), 79988)

    def test_expPowerOf256_32(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: expPowerOf256_32.json
        sha256sum: b44ae8df0e423ad89f67faa99b4a982ee5bf923f0f585a35cec69259f6f8fa71
        Code:     PUSH1 0x20
                  PUSH2 0x100
                  EXP
                  PUSH1 0x0
                  SSTORE
                  PUSH1 0x20
                  PUSH1 0xff
                  EXP
                  PUSH1 0x1
                  SSTORE
                  PUSH1 0x20
                  PUSH2 0x101
                  EXP
                  PUSH1 0x2
                  SSTORE
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
        acc_code = unhexlify("60206101000a600055602060ff0a60015560206101010a600255")
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F2947DEF4CF144679DA39C4C32BDC35681
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

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 0)
        self.assertEqual(
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 1000000000000000000
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6),
            unhexlify("60206101000a600055602060ff0a60015560206101010a600255"),
        )
        # check storage
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x01)),
            0xE1DD29730112F6EF1D8EDABFD4C3C60C823D865CD592ABCDF0BDEC64A1EFE001,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x02)),
            0x2203EF98A7CE0EF9BF3C04038583F6B2AB4D27E3ED8E5285B6E32C8B61F02001,
        )
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
        self.assertEqual(solve(world.current_vm.gas), 54913)

    def test_div1(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: div1.json
        sha256sum: 9a5f11688d430e2cb5f9b54e4a4cd6ff8ab60e7507cd3aed74f906c844a9510b
        Code:     PUSH1 0x2
                  PUSH32 0xfedcba9876543210fedcba9876543210fedcba9876543210fedcba9876543210
                  DIV
                  PUSH1 0x0
                  MSTORE
                  PUSH1 0x20
                  PUSH1 0x0
                  RETURN
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
        acc_code = unhexlify(
            "60027ffedcba9876543210fedcba9876543210fedcba9876543210fedcba98765432100460005260206000f3"
        )
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F2947DEF4CF144679DA39C4C32BDC35681
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

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 0)
        self.assertEqual(
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 1000000000000000000
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6),
            unhexlify(
                "60027ffedcba9876543210fedcba9876543210fedcba9876543210fedcba98765432100460005260206000f3"
            ),
        )
        # check outs
        self.assertEqual(
            returndata,
            unhexlify("7f6e5d4c3b2a19087f6e5d4c3b2a19087f6e5d4c3b2a19087f6e5d4c3b2a1908"),
        )
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
        self.assertEqual(solve(world.current_vm.gas), 99974)

    def test_mulmod1(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: mulmod1.json
        sha256sum: 0627eddadc1ab556e263b67f4cf1a33102073c638f800756cfec5eefd47161c7
        Code:     PUSH1 0x3
                  PUSH1 0x2
                  PUSH1 0x0
                  SUB
                  PUSH1 0x1
                  PUSH1 0x0
                  SUB
                  MULMOD
                  PUSH1 0x0
                  SSTORE
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
        acc_code = unhexlify("60036002600003600160000309600055")
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F2947DEF4CF144679DA39C4C32BDC35681
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

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 0)
        self.assertEqual(
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 1000000000000000000
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6),
            unhexlify("60036002600003600160000309600055"),
        )
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
        self.assertEqual(solve(world.current_vm.gas), 94968)

    def test_mulmod1_overflow(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: mulmod1_overflow.json
        sha256sum: 12d71b58080463465d8822d3b6629037f70dd2f8724cc2f287c7e3c8e31ee88f
        Code:     PUSH1 0x5
                  PUSH1 0x2
                  PUSH1 0x1
                  PUSH1 0x0
                  SUB
                  MULMOD
                  PUSH1 0x0
                  SSTORE
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
        acc_code = unhexlify("60056002600160000309600055")
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F2947DEF4CF144679DA39C4C32BDC35681
        price = 0x5AF3107A4000
        value = 1000000000000000000
        gas = 10000
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

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 0)
        self.assertEqual(
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 1000000000000000000
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6),
            unhexlify("60056002600160000309600055"),
        )
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
        self.assertEqual(solve(world.current_vm.gas), 4974)

    def test_mod2(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: mod2.json
        sha256sum: 27dc39b0ff64dfc9c5b2a79c0f75ecc32cad7ecded7d9ae1debdf1ffc4787d1d
        Code:     PUSH32 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
                  PUSH1 0x0
                  MOD
                  PUSH1 0x0
                  SSTORE
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
        acc_code = unhexlify(
            "7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff600006600055"
        )
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F2947DEF4CF144679DA39C4C32BDC35681
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

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 0)
        self.assertEqual(
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 1000000000000000000
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6),
            unhexlify(
                "7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff600006600055"
            ),
        )
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
        self.assertEqual(solve(world.current_vm.gas), 94986)

    def test_mulmod2(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: mulmod2.json
        sha256sum: 6e8dc3cc2c5f0a7eb90d7aaa90a0253d7062c6e750554e6a44f1d711115ebb34
        Code:     PUSH1 0x3
                  PUSH1 0x1
                  PUSH1 0x5
                  PUSH1 0x0
                  SUB
                  MULMOD
                  PUSH1 0x0
                  SSTORE
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
        acc_code = unhexlify("60036001600560000309600055")
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F2947DEF4CF144679DA39C4C32BDC35681
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

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 0)
        self.assertEqual(
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 1000000000000000000
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6),
            unhexlify("60036001600560000309600055"),
        )
        # check storage
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x00)), 0x02
        )
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
        self.assertEqual(solve(world.current_vm.gas), 79974)

    def test_mulmod0(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: mulmod0.json
        sha256sum: 82bfcdf4dcf1fdeb40788305eee151381ec460d0213106206899051184c39283
        Code:     PUSH1 0x2
                  PUSH1 0x2
                  PUSH1 0x1
                  MULMOD
                  PUSH1 0x0
                  SSTORE
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
        acc_code = unhexlify("60026002600109600055")
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F2947DEF4CF144679DA39C4C32BDC35681
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

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 0)
        self.assertEqual(
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 1000000000000000000
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6),
            unhexlify("60026002600109600055"),
        )
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
        self.assertEqual(solve(world.current_vm.gas), 94980)

    def test_expPowerOf256Of256_11(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: expPowerOf256Of256_11.json
        sha256sum: c095d37a7b0eb417879abbe3066683a970ac925a68661ac9908ad4f16c9774c4
        Code:     PUSH1 0xb
                  PUSH2 0x100
                  EXP
                  PUSH2 0x100
                  EXP
                  PUSH1 0x0
                  SSTORE
                  PUSH1 0xb
                  PUSH1 0xff
                  EXP
                  PUSH2 0x100
                  EXP
                  PUSH1 0x1
                  SSTORE
                  PUSH1 0xb
                  PUSH2 0x101
                  EXP
                  PUSH2 0x100
                  EXP
                  PUSH1 0x2
                  SSTORE
                  PUSH1 0xb
                  PUSH2 0x100
                  EXP
                  PUSH1 0xff
                  EXP
                  PUSH1 0x3
                  SSTORE
                  PUSH1 0xb
                  PUSH1 0xff
                  EXP
                  PUSH1 0xff
                  EXP
                  PUSH1 0x4
                  SSTORE
                  PUSH1 0xb
                  PUSH2 0x101
                  EXP
                  PUSH1 0xff
                  EXP
                  PUSH1 0x5
                  SSTORE
                  PUSH1 0xb
                  PUSH2 0x100
                  EXP
                  PUSH2 0x101
                  EXP
                  PUSH1 0x6
                  SSTORE
                  PUSH1 0xb
                  PUSH1 0xff
                  EXP
                  PUSH2 0x101
                  EXP
                  PUSH1 0x7
                  SSTORE
                  PUSH1 0xb
                  PUSH2 0x101
                  EXP
                  PUSH2 0x101
                  EXP
                  PUSH1 0x8
                  SSTORE
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
        gaslimit = 10000000
        world = evm.EVMWorld(
            constraints,
            blocknumber=blocknumber,
            timestamp=timestamp,
            difficulty=difficulty,
            coinbase=coinbase,
            gaslimit=gaslimit,
        )

        acc_addr = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        acc_code = unhexlify(
            "600b6101000a6101000a600055600b60ff0a6101000a600155600b6101010a6101000a600255600b6101000a60ff0a600355600b60ff0a60ff0a600455600b6101010a60ff0a600555600b6101000a6101010a600655600b60ff0a6101010a600755600b6101010a6101010a600855"
        )
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F2947DEF4CF144679DA39C4C32BDC35681
        price = 0x5AF3107A4000
        value = 1000000000000000000
        gas = 1000000
        data = ""
        # open a fake tx, no funds send
        world._open_transaction("CALL", address, price, data, caller, value, gas=gas)

        # This variable might seem redundant in some tests - don't forget it is auto generated
        # and there are cases in which we need it ;)
        result, returndata = self._test_run(world)

        # World sanity checks - those should not change, right?
        self.assertEqual(solve(world.block_number()), 0)
        self.assertEqual(solve(world.block_gaslimit()), 10000000)
        self.assertEqual(solve(world.block_timestamp()), 1)
        self.assertEqual(solve(world.block_difficulty()), 256)
        self.assertEqual(solve(world.block_coinbase()), 0x2ADC25665018AA1FE0E6BC666DAC8FC2697FF9BA)

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 0)
        self.assertEqual(
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 1000000000000000000
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6),
            unhexlify(
                "600b6101000a6101000a600055600b60ff0a6101000a600155600b6101010a6101000a600255600b6101000a60ff0a600355600b60ff0a60ff0a600455600b6101010a60ff0a600555600b6101000a6101010a600655600b60ff0a6101010a600755600b6101010a6101010a600855"
            ),
        )
        # check storage
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x03)),
            0xE1440264B8EE0CEA0218879EC55C33085514FF7F000000000000000000000001,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x04)),
            0x29575FDCE377B23043E489E358581474BC863187FA85F9945473A2BE5889FEFF,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x05)),
            0x3DF8C030EC521FB109C4D887DBBC14C7C9C9921B27058E3503971B60B18B00FF,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x06)),
            0x67799740340DAF4A30F000B68FB921F7AA6AFF81000000000000000000000001,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x07)),
            0x540A4E4635B40585E09FF10B63FFE310DD717FCA5C0A51570091E25E378BFF01,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x08)),
            0xDBBAEF5C49FFEE61B08CDE6EBC8DBA6E9A62D56C2355D1980CB9E790BC8B0101,
        )
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
        self.assertEqual(solve(world.current_vm.gas), 863572)

    def test_mulUnderFlow(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: mulUnderFlow.json
        sha256sum: 07f33220f500f3cff0eb048aa153f3b56b5442c84a28b3c893559d7aa6d57769
        Code:     PUSH1 0x1
                  MUL
                  PUSH1 0x1
                  SSTORE
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
        acc_code = unhexlify("600102600155")
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F2947DEF4CF144679DA39C4C32BDC35681
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

        # If test end in exception check it here
        self.assertTrue(result == "THROW")

    def test_expPowerOf256_10(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: expPowerOf256_10.json
        sha256sum: 141e97d2625d720bc8e55bb0a9871fa8eb6120d563da1f64d8a2945be4ec018c
        Code:     PUSH1 0xa
                  PUSH2 0x100
                  EXP
                  PUSH1 0x0
                  SSTORE
                  PUSH1 0xa
                  PUSH1 0xff
                  EXP
                  PUSH1 0x1
                  SSTORE
                  PUSH1 0xa
                  PUSH2 0x101
                  EXP
                  PUSH1 0x2
                  SSTORE
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
        acc_code = unhexlify("600a6101000a600055600a60ff0a600155600a6101010a600255")
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F2947DEF4CF144679DA39C4C32BDC35681
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

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 0)
        self.assertEqual(
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 1000000000000000000
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6),
            unhexlify("600a6101000a600055600a60ff0a600155600a6101010a600255"),
        )
        # check storage
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x00)),
            0x0100000000000000000000,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x01)),
            0xF62C88D104D1882CF601,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x02)),
            0x010A2D78D2FCD2782D0A01,
        )
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
        self.assertEqual(solve(world.current_vm.gas), 39913)

    def test_addmod1_overflow3(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: addmod1_overflow3.json
        sha256sum: dcf46135e92be5e31ad5395de44fdce8d6c44c2a594712ebd9c6c79b560efef4
        Code:     PUSH1 0x5
                  PUSH1 0x1
                  PUSH1 0x1
                  PUSH1 0x0
                  SUB
                  ADDMOD
                  PUSH1 0x0
                  SSTORE
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
        acc_code = unhexlify("60056001600160000308600055")
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F2947DEF4CF144679DA39C4C32BDC35681
        price = 0x5AF3107A4000
        value = 1000000000000000000
        gas = 1000000
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

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 0)
        self.assertEqual(
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 1000000000000000000
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6),
            unhexlify("60056001600160000308600055"),
        )
        # check storage
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x00)), 0x01
        )
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
        self.assertEqual(solve(world.current_vm.gas), 979974)

    def test_exp5(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: exp5.json
        sha256sum: ad4694559220ec79dde1ec9c646d8629e4ad97510b81eb2173a727ce3f1d6c1e
        Code:     PUSH1 0x1
                  PUSH2 0x101
                  EXP
                  PUSH1 0x0
                  SSTORE
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
        acc_code = unhexlify("60016101010a600055")
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F2947DEF4CF144679DA39C4C32BDC35681
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

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 0)
        self.assertEqual(
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 1000000000000000000
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6),
            unhexlify("60016101010a600055"),
        )
        # check storage
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x00)), 0x0101
        )
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
        self.assertEqual(solve(world.current_vm.gas), 79971)

    def test_expPowerOf256Of256_10(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: expPowerOf256Of256_10.json
        sha256sum: 0248bad71261f2ebe6476f4ed0ca91e98062b440c738386dde95fc76da51e826
        Code:     PUSH1 0xa
                  PUSH2 0x100
                  EXP
                  PUSH2 0x100
                  EXP
                  PUSH1 0x0
                  SSTORE
                  PUSH1 0xa
                  PUSH1 0xff
                  EXP
                  PUSH2 0x100
                  EXP
                  PUSH1 0x1
                  SSTORE
                  PUSH1 0xa
                  PUSH2 0x101
                  EXP
                  PUSH2 0x100
                  EXP
                  PUSH1 0x2
                  SSTORE
                  PUSH1 0xa
                  PUSH2 0x100
                  EXP
                  PUSH1 0xff
                  EXP
                  PUSH1 0x3
                  SSTORE
                  PUSH1 0xa
                  PUSH1 0xff
                  EXP
                  PUSH1 0xff
                  EXP
                  PUSH1 0x4
                  SSTORE
                  PUSH1 0xa
                  PUSH2 0x101
                  EXP
                  PUSH1 0xff
                  EXP
                  PUSH1 0x5
                  SSTORE
                  PUSH1 0xa
                  PUSH2 0x100
                  EXP
                  PUSH2 0x101
                  EXP
                  PUSH1 0x6
                  SSTORE
                  PUSH1 0xa
                  PUSH1 0xff
                  EXP
                  PUSH2 0x101
                  EXP
                  PUSH1 0x7
                  SSTORE
                  PUSH1 0xa
                  PUSH2 0x101
                  EXP
                  PUSH2 0x101
                  EXP
                  PUSH1 0x8
                  SSTORE
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
        gaslimit = 10000000
        world = evm.EVMWorld(
            constraints,
            blocknumber=blocknumber,
            timestamp=timestamp,
            difficulty=difficulty,
            coinbase=coinbase,
            gaslimit=gaslimit,
        )

        acc_addr = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        acc_code = unhexlify(
            "600a6101000a6101000a600055600a60ff0a6101000a600155600a6101010a6101000a600255600a6101000a60ff0a600355600a60ff0a60ff0a600455600a6101010a60ff0a600555600a6101000a6101010a600655600a60ff0a6101010a600755600a6101010a6101010a600855"
        )
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F2947DEF4CF144679DA39C4C32BDC35681
        price = 0x5AF3107A4000
        value = 1000000000000000000
        gas = 1000000
        data = ""
        # open a fake tx, no funds send
        world._open_transaction("CALL", address, price, data, caller, value, gas=gas)

        # This variable might seem redundant in some tests - don't forget it is auto generated
        # and there are cases in which we need it ;)
        result, returndata = self._test_run(world)

        # World sanity checks - those should not change, right?
        self.assertEqual(solve(world.block_number()), 0)
        self.assertEqual(solve(world.block_gaslimit()), 10000000)
        self.assertEqual(solve(world.block_timestamp()), 1)
        self.assertEqual(solve(world.block_difficulty()), 256)
        self.assertEqual(solve(world.block_coinbase()), 0x2ADC25665018AA1FE0E6BC666DAC8FC2697FF9BA)

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 0)
        self.assertEqual(
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 1000000000000000000
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6),
            unhexlify(
                "600a6101000a6101000a600055600a60ff0a6101000a600155600a6101010a6101000a600255600a6101000a60ff0a600355600a60ff0a60ff0a600455600a6101010a60ff0a600555600a6101000a6101010a600655600a60ff0a6101010a600755600a6101010a6101010a600855"
            ),
        )
        # check storage
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x03)),
            0xFE0F60957DC223578A0298879EC55C33085514FF7F0000000000000000000001,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x04)),
            0xC1EA45F348B5D351C4D8FE5C77DA979CADC33D866ACC42E981278896B1F600FF,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x05)),
            0x56DDB29BCA94FB986AC0A40188B3B53F3216B3559BD8324A77EA8BD8A80A00FF,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x06)),
            0x2D49FF6B0BBE177AE9317000B68FB921F7AA6AFF810000000000000000000001,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x07)),
            0x185FA9EAB94CFE3016B69657E83B23FD24CC6960218254231C3DB627A7F60101,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x08)),
            0xA7A0223829F26D6C635368034320563DF4AA5EB62EFC87A42BB35F69B20A0101,
        )
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
        self.assertEqual(solve(world.current_vm.gas), 863662)

    def test_expPowerOf256_27(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: expPowerOf256_27.json
        sha256sum: f1fa279d11f40fe6dde87ae675344583f0fad34b69ff60a946544969e6af9c7f
        Code:     PUSH1 0x1b
                  PUSH2 0x100
                  EXP
                  PUSH1 0x0
                  SSTORE
                  PUSH1 0x1b
                  PUSH1 0xff
                  EXP
                  PUSH1 0x1
                  SSTORE
                  PUSH1 0x1b
                  PUSH2 0x101
                  EXP
                  PUSH1 0x2
                  SSTORE
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
        acc_code = unhexlify("601b6101000a600055601b60ff0a600155601b6101010a600255")
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F2947DEF4CF144679DA39C4C32BDC35681
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

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 0)
        self.assertEqual(
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 1000000000000000000
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6),
            unhexlify("601b6101000a600055601b60ff0a600155601b6101010a600255"),
        )
        # check storage
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x00)),
            0x01000000000000000000000000000000000000000000000000000000,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x01)),
            0xE653D6571CDEBB270B53C9D44C40BCD425165D5AF1157D6BA11AFF,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x02)),
            0x011C6AB2CDEBF906306B38BBF7D6C52648E2D6BC63859E996E5F1B01,
        )
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
        self.assertEqual(solve(world.current_vm.gas), 39913)

    def test_mul2(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: mul2.json
        sha256sum: ded58f693df18ced862fde46ba5b800217564648c15f2c6ec9c09545ba9d454b
        Code:     PUSH1 0x17
                  PUSH1 0x0
                  MUL
                  PUSH1 0x0
                  SSTORE
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
        acc_code = unhexlify("6017600002600055")
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F2947DEF4CF144679DA39C4C32BDC35681
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

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 0)
        self.assertEqual(
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 1000000000000000000
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6), unhexlify("6017600002600055")
        )
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
        self.assertEqual(solve(world.current_vm.gas), 94986)

    def test_expPowerOf256Of256_25(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: expPowerOf256Of256_25.json
        sha256sum: ba80c4646a1371e93e9ecd024b52b25819963d880c6cef7a37dc515d93cc9dca
        Code:     PUSH1 0x19
                  PUSH2 0x100
                  EXP
                  PUSH2 0x100
                  EXP
                  PUSH1 0x0
                  SSTORE
                  PUSH1 0x19
                  PUSH1 0xff
                  EXP
                  PUSH2 0x100
                  EXP
                  PUSH1 0x1
                  SSTORE
                  PUSH1 0x19
                  PUSH2 0x101
                  EXP
                  PUSH2 0x100
                  EXP
                  PUSH1 0x2
                  SSTORE
                  PUSH1 0x19
                  PUSH2 0x100
                  EXP
                  PUSH1 0xff
                  EXP
                  PUSH1 0x3
                  SSTORE
                  PUSH1 0x19
                  PUSH1 0xff
                  EXP
                  PUSH1 0xff
                  EXP
                  PUSH1 0x4
                  SSTORE
                  PUSH1 0x19
                  PUSH2 0x101
                  EXP
                  PUSH1 0xff
                  EXP
                  PUSH1 0x5
                  SSTORE
                  PUSH1 0x19
                  PUSH2 0x100
                  EXP
                  PUSH2 0x101
                  EXP
                  PUSH1 0x6
                  SSTORE
                  PUSH1 0x19
                  PUSH1 0xff
                  EXP
                  PUSH2 0x101
                  EXP
                  PUSH1 0x7
                  SSTORE
                  PUSH1 0x19
                  PUSH2 0x101
                  EXP
                  PUSH2 0x101
                  EXP
                  PUSH1 0x8
                  SSTORE
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
        gaslimit = 10000000
        world = evm.EVMWorld(
            constraints,
            blocknumber=blocknumber,
            timestamp=timestamp,
            difficulty=difficulty,
            coinbase=coinbase,
            gaslimit=gaslimit,
        )

        acc_addr = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        acc_code = unhexlify(
            "60196101000a6101000a600055601960ff0a6101000a60015560196101010a6101000a60025560196101000a60ff0a600355601960ff0a60ff0a60045560196101010a60ff0a60055560196101000a6101010a600655601960ff0a6101010a60075560196101010a6101010a600855"
        )
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F2947DEF4CF144679DA39C4C32BDC35681
        price = 0x5AF3107A4000
        value = 1000000000000000000
        gas = 1000000
        data = ""
        # open a fake tx, no funds send
        world._open_transaction("CALL", address, price, data, caller, value, gas=gas)

        # This variable might seem redundant in some tests - don't forget it is auto generated
        # and there are cases in which we need it ;)
        result, returndata = self._test_run(world)

        # World sanity checks - those should not change, right?
        self.assertEqual(solve(world.block_number()), 0)
        self.assertEqual(solve(world.block_gaslimit()), 10000000)
        self.assertEqual(solve(world.block_timestamp()), 1)
        self.assertEqual(solve(world.block_difficulty()), 256)
        self.assertEqual(solve(world.block_coinbase()), 0x2ADC25665018AA1FE0E6BC666DAC8FC2697FF9BA)

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 0)
        self.assertEqual(
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 1000000000000000000
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6),
            unhexlify(
                "60196101000a6101000a600055601960ff0a6101000a60015560196101010a6101000a60025560196101000a60ff0a600355601960ff0a60ff0a60045560196101010a60ff0a60055560196101000a6101010a600655601960ff0a6101010a60075560196101010a6101010a600855"
            ),
        )
        # check storage
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x03)),
            0x33085514FF7F0000000000000000000000000000000000000000000000000001,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x04)),
            0x7F510DD7198CAC0A92FF7EA80451838C0DFA12114C41A0EF05907397F897FEFF,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x05)),
            0x1275E752B6AEE228ECBA5E9B57EF1111DEFF3C651E2CFBF2CCCD13151F9900FF,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x06)),
            0x21F7AA6AFF810000000000000000000000000000000000000000000000000001,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x07)),
            0x6646340AD51A03BB710CAF05756B685B33C7DAD62AE68D369243700EAD99FF01,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x08)),
            0x29D80E8060EF2221929BB18215586C742686D6860E028CA0456B443238990101,
        )
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
        self.assertEqual(solve(world.current_vm.gas), 862312)

    def test_signextend_0_BigByte(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: signextend_0_BigByte.json
        sha256sum: 424909bbf0356303bb5a4abef2cb932c66fb55f2db46dd22eba088eabf61a168
        Code:     PUSH32 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
                  PUSH1 0x0
                  SIGNEXTEND
                  PUSH1 0x0
                  SSTORE
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
        gaslimit = 10000000
        world = evm.EVMWorld(
            constraints,
            blocknumber=blocknumber,
            timestamp=timestamp,
            difficulty=difficulty,
            coinbase=coinbase,
            gaslimit=gaslimit,
        )

        acc_addr = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        acc_code = unhexlify(
            "7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff60000b600055"
        )
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F2947DEF4CF144679DA39C4C32BDC35681
        price = 0x5AF3107A4000
        value = 1000000000000000000
        gas = 1000000
        data = ""
        # open a fake tx, no funds send
        world._open_transaction("CALL", address, price, data, caller, value, gas=gas)

        # This variable might seem redundant in some tests - don't forget it is auto generated
        # and there are cases in which we need it ;)
        result, returndata = self._test_run(world)

        # World sanity checks - those should not change, right?
        self.assertEqual(solve(world.block_number()), 0)
        self.assertEqual(solve(world.block_gaslimit()), 10000000)
        self.assertEqual(solve(world.block_timestamp()), 1)
        self.assertEqual(solve(world.block_difficulty()), 256)
        self.assertEqual(solve(world.block_coinbase()), 0x2ADC25665018AA1FE0E6BC666DAC8FC2697FF9BA)

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 0)
        self.assertEqual(
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 1000000000000000000
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6),
            unhexlify(
                "7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff60000b600055"
            ),
        )
        # check storage
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x00)),
            0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF,
        )
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
        self.assertEqual(solve(world.current_vm.gas), 979986)

    def test_addmod1_overflowDiff(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: addmod1_overflowDiff.json
        sha256sum: 8609abdac8c8de1a6b70f84ffbc4be546844b9c77c6a9e9fa35fd7f987e3fb4c
        Code:     PUSH1 0x5
                  PUSH1 0x2
                  PUSH1 0x0
                  SUB
                  PUSH1 0x1
                  PUSH1 0x0
                  SUB
                  ADDMOD
                  PUSH1 0x0
                  SSTORE
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
        acc_code = unhexlify("60056002600003600160000308600055")
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F2947DEF4CF144679DA39C4C32BDC35681
        price = 0x5AF3107A4000
        value = 1000000000000000000
        gas = 1000000
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

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 0)
        self.assertEqual(
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 1000000000000000000
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6),
            unhexlify("60056002600003600160000308600055"),
        )
        # check storage
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x00)), 0x04
        )
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
        self.assertEqual(solve(world.current_vm.gas), 979968)

    def test_addmod0(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: addmod0.json
        sha256sum: 515208833995d0cf1a7bc89bfef6fb4fd04a059bbdb4187cadc423b99bff0c71
        Code:     PUSH1 0x2
                  PUSH1 0x2
                  PUSH1 0x1
                  ADDMOD
                  PUSH1 0x0
                  SSTORE
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
        acc_code = unhexlify("60026002600108600055")
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F2947DEF4CF144679DA39C4C32BDC35681
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

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 0)
        self.assertEqual(
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 1000000000000000000
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6),
            unhexlify("60026002600108600055"),
        )
        # check storage
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x00)), 0x01
        )
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
        self.assertEqual(solve(world.current_vm.gas), 79980)

    def test_addmod3_0(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: addmod3_0.json
        sha256sum: bd94167768aaa9089feaf9ea004aee1cd7728ce0beb00313054d245e41641ba0
        Code:     PUSH1 0x2
                  PUSH1 0x3
                  PUSH1 0x0
                  SUB
                  PUSH1 0x1
                  PUSH1 0x4
                  ADDMOD
                  EQ
                  PUSH1 0x0
                  SSTORE
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
        acc_code = unhexlify("60026003600003600160040814600055")
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F2947DEF4CF144679DA39C4C32BDC35681
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

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 0)
        self.assertEqual(
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 1000000000000000000
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6),
            unhexlify("60026003600003600160040814600055"),
        )
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
        self.assertEqual(solve(world.current_vm.gas), 94968)

    def test_expPowerOf256_14(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: expPowerOf256_14.json
        sha256sum: 73f9ef5771c69fa8a9b4909d382d9c0938efdff9df3db88e2597aa71dbfbf76f
        Code:     PUSH1 0xe
                  PUSH2 0x100
                  EXP
                  PUSH1 0x0
                  SSTORE
                  PUSH1 0xe
                  PUSH1 0xff
                  EXP
                  PUSH1 0x1
                  SSTORE
                  PUSH1 0xe
                  PUSH2 0x101
                  EXP
                  PUSH1 0x2
                  SSTORE
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
        acc_code = unhexlify("600e6101000a600055600e60ff0a600155600e6101010a600255")
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F2947DEF4CF144679DA39C4C32BDC35681
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

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 0)
        self.assertEqual(
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 1000000000000000000
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6),
            unhexlify("600e6101000a600055600e60ff0a600155600e6101010a600255"),
        )
        # check storage
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x00)),
            0x010000000000000000000000000000,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x01)),
            0xF25997E139ADA3B331E7945AF201,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x02)),
            0x010E5C6FF0DDC873C2D5EA6C5B0E01,
        )
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
        self.assertEqual(solve(world.current_vm.gas), 39913)

    def test_expPowerOf256Of256_23(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: expPowerOf256Of256_23.json
        sha256sum: f07022f79f143cb93c4ec3883ae3438038e6945295ec29f1f268e95a90e19fca
        Code:     PUSH1 0x17
                  PUSH2 0x100
                  EXP
                  PUSH2 0x100
                  EXP
                  PUSH1 0x0
                  SSTORE
                  PUSH1 0x17
                  PUSH1 0xff
                  EXP
                  PUSH2 0x100
                  EXP
                  PUSH1 0x1
                  SSTORE
                  PUSH1 0x17
                  PUSH2 0x101
                  EXP
                  PUSH2 0x100
                  EXP
                  PUSH1 0x2
                  SSTORE
                  PUSH1 0x17
                  PUSH2 0x100
                  EXP
                  PUSH1 0xff
                  EXP
                  PUSH1 0x3
                  SSTORE
                  PUSH1 0x17
                  PUSH1 0xff
                  EXP
                  PUSH1 0xff
                  EXP
                  PUSH1 0x4
                  SSTORE
                  PUSH1 0x17
                  PUSH2 0x101
                  EXP
                  PUSH1 0xff
                  EXP
                  PUSH1 0x5
                  SSTORE
                  PUSH1 0x17
                  PUSH2 0x100
                  EXP
                  PUSH2 0x101
                  EXP
                  PUSH1 0x6
                  SSTORE
                  PUSH1 0x17
                  PUSH1 0xff
                  EXP
                  PUSH2 0x101
                  EXP
                  PUSH1 0x7
                  SSTORE
                  PUSH1 0x17
                  PUSH2 0x101
                  EXP
                  PUSH2 0x101
                  EXP
                  PUSH1 0x8
                  SSTORE
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
        gaslimit = 10000000
        world = evm.EVMWorld(
            constraints,
            blocknumber=blocknumber,
            timestamp=timestamp,
            difficulty=difficulty,
            coinbase=coinbase,
            gaslimit=gaslimit,
        )

        acc_addr = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        acc_code = unhexlify(
            "60176101000a6101000a600055601760ff0a6101000a60015560176101010a6101000a60025560176101000a60ff0a600355601760ff0a60ff0a60045560176101010a60ff0a60055560176101000a6101010a600655601760ff0a6101010a60075560176101010a6101010a600855"
        )
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F2947DEF4CF144679DA39C4C32BDC35681
        price = 0x5AF3107A4000
        value = 1000000000000000000
        gas = 1000000
        data = ""
        # open a fake tx, no funds send
        world._open_transaction("CALL", address, price, data, caller, value, gas=gas)

        # This variable might seem redundant in some tests - don't forget it is auto generated
        # and there are cases in which we need it ;)
        result, returndata = self._test_run(world)

        # World sanity checks - those should not change, right?
        self.assertEqual(solve(world.block_number()), 0)
        self.assertEqual(solve(world.block_gaslimit()), 10000000)
        self.assertEqual(solve(world.block_timestamp()), 1)
        self.assertEqual(solve(world.block_difficulty()), 256)
        self.assertEqual(solve(world.block_coinbase()), 0x2ADC25665018AA1FE0E6BC666DAC8FC2697FF9BA)

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 0)
        self.assertEqual(
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 1000000000000000000
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6),
            unhexlify(
                "60176101000a6101000a600055601760ff0a6101000a60015560176101010a6101000a60025560176101000a60ff0a600355601760ff0a60ff0a60045560176101010a60ff0a60055560176101000a6101010a600655601760ff0a6101010a60075560176101010a6101010a600855"
            ),
        )
        # check storage
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x03)),
            0xC55C33085514FF7F000000000000000000000000000000000000000000000001,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x04)),
            0x537CA0F03F974303005F1E6693B55B72315A166841732E42B8353724A495FEFF,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x05)),
            0x86418797EC60058DE6CCA47DFDBEE79923AC49D7801E01840041CA76719700FF,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x06)),
            0x8FB921F7AA6AFF81000000000000000000000000000000000000000000000001,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x07)),
            0x56A55341AB8D4318F1CFB55D5F21E2BA35D7E070A72BAC6B2B21BAAE5F97FF01,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x08)),
            0x55DDD0EC77909DE6D8311116CF520398E816F928B06FDD90EC239D0488970101,
        )
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
        self.assertEqual(solve(world.current_vm.gas), 862492)

    def test_signextend_00(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: signextend_00.json
        sha256sum: 557642b12d33eba0059e417c929fd5700c9e530b97bec89c3a5e154d6539c117
        Code:     PUSH1 0x0
                  PUSH1 0x0
                  SIGNEXTEND
                  PUSH1 0x0
                  SSTORE
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
        gaslimit = 10000000
        world = evm.EVMWorld(
            constraints,
            blocknumber=blocknumber,
            timestamp=timestamp,
            difficulty=difficulty,
            coinbase=coinbase,
            gaslimit=gaslimit,
        )

        acc_addr = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        acc_code = unhexlify("600060000b600055")
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F2947DEF4CF144679DA39C4C32BDC35681
        price = 0x5AF3107A4000
        value = 1000000000000000000
        gas = 1000000
        data = ""
        # open a fake tx, no funds send
        world._open_transaction("CALL", address, price, data, caller, value, gas=gas)

        # This variable might seem redundant in some tests - don't forget it is auto generated
        # and there are cases in which we need it ;)
        result, returndata = self._test_run(world)

        # World sanity checks - those should not change, right?
        self.assertEqual(solve(world.block_number()), 0)
        self.assertEqual(solve(world.block_gaslimit()), 10000000)
        self.assertEqual(solve(world.block_timestamp()), 1)
        self.assertEqual(solve(world.block_difficulty()), 256)
        self.assertEqual(solve(world.block_coinbase()), 0x2ADC25665018AA1FE0E6BC666DAC8FC2697FF9BA)

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 0)
        self.assertEqual(
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 1000000000000000000
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6), unhexlify("600060000b600055")
        )
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
        self.assertEqual(solve(world.current_vm.gas), 994986)

    def test_addmod1_overflow4(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: addmod1_overflow4.json
        sha256sum: fe6cf50ca2f047306b0651dc05dad77abfd1020d720c8f7f9a3ce880e7c1a883
        Code:     PUSH1 0x5
                  PUSH1 0x2
                  PUSH1 0x1
                  PUSH1 0x0
                  SUB
                  ADDMOD
                  PUSH1 0x0
                  SSTORE
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
        acc_code = unhexlify("60056002600160000308600055")
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F2947DEF4CF144679DA39C4C32BDC35681
        price = 0x5AF3107A4000
        value = 1000000000000000000
        gas = 1000000
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

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 0)
        self.assertEqual(
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 1000000000000000000
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6),
            unhexlify("60056002600160000308600055"),
        )
        # check storage
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x00)), 0x02
        )
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
        self.assertEqual(solve(world.current_vm.gas), 979974)

    def test_smod2(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: smod2.json
        sha256sum: 78f2af60323f8507b529824bbe23ce7fbdf5f722392b97db8e3b1b7b348c8b05
        Code:     PUSH1 0x3
                  PUSH1 0x5
                  PUSH1 0x0
                  SUB
                  SMOD
                  PUSH1 0x0
                  SSTORE
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
        acc_code = unhexlify("6003600560000307600055")
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F2947DEF4CF144679DA39C4C32BDC35681
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

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 0)
        self.assertEqual(
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 1000000000000000000
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6),
            unhexlify("6003600560000307600055"),
        )
        # check storage
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x00)),
            0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFE,
        )
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
        self.assertEqual(solve(world.current_vm.gas), 79980)

    def test_expPowerOf256Of256_6(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: expPowerOf256Of256_6.json
        sha256sum: a5e79941b4ad22e16675c01093e4641e21c12e304fb056cd48e99cd32659982e
        Code:     PUSH1 0x6
                  PUSH2 0x100
                  EXP
                  PUSH2 0x100
                  EXP
                  PUSH1 0x0
                  SSTORE
                  PUSH1 0x6
                  PUSH1 0xff
                  EXP
                  PUSH2 0x100
                  EXP
                  PUSH1 0x1
                  SSTORE
                  PUSH1 0x6
                  PUSH2 0x101
                  EXP
                  PUSH2 0x100
                  EXP
                  PUSH1 0x2
                  SSTORE
                  PUSH1 0x6
                  PUSH2 0x100
                  EXP
                  PUSH1 0xff
                  EXP
                  PUSH1 0x3
                  SSTORE
                  PUSH1 0x6
                  PUSH1 0xff
                  EXP
                  PUSH1 0xff
                  EXP
                  PUSH1 0x4
                  SSTORE
                  PUSH1 0x6
                  PUSH2 0x101
                  EXP
                  PUSH1 0xff
                  EXP
                  PUSH1 0x5
                  SSTORE
                  PUSH1 0x6
                  PUSH2 0x100
                  EXP
                  PUSH2 0x101
                  EXP
                  PUSH1 0x6
                  SSTORE
                  PUSH1 0x6
                  PUSH1 0xff
                  EXP
                  PUSH2 0x101
                  EXP
                  PUSH1 0x7
                  SSTORE
                  PUSH1 0x6
                  PUSH2 0x101
                  EXP
                  PUSH2 0x101
                  EXP
                  PUSH1 0x8
                  SSTORE
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
        gaslimit = 10000000
        world = evm.EVMWorld(
            constraints,
            blocknumber=blocknumber,
            timestamp=timestamp,
            difficulty=difficulty,
            coinbase=coinbase,
            gaslimit=gaslimit,
        )

        acc_addr = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        acc_code = unhexlify(
            "60066101000a6101000a600055600660ff0a6101000a60015560066101010a6101000a60025560066101000a60ff0a600355600660ff0a60ff0a60045560066101010a60ff0a60055560066101000a6101010a600655600660ff0a6101010a60075560066101010a6101010a600855"
        )
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F2947DEF4CF144679DA39C4C32BDC35681
        price = 0x5AF3107A4000
        value = 1000000000000000000
        gas = 1000000
        data = ""
        # open a fake tx, no funds send
        world._open_transaction("CALL", address, price, data, caller, value, gas=gas)

        # This variable might seem redundant in some tests - don't forget it is auto generated
        # and there are cases in which we need it ;)
        result, returndata = self._test_run(world)

        # World sanity checks - those should not change, right?
        self.assertEqual(solve(world.block_number()), 0)
        self.assertEqual(solve(world.block_gaslimit()), 10000000)
        self.assertEqual(solve(world.block_timestamp()), 1)
        self.assertEqual(solve(world.block_difficulty()), 256)
        self.assertEqual(solve(world.block_coinbase()), 0x2ADC25665018AA1FE0E6BC666DAC8FC2697FF9BA)

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 0)
        self.assertEqual(
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 1000000000000000000
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6),
            unhexlify(
                "60066101000a6101000a600055600660ff0a6101000a60015560066101010a6101000a60025560066101000a60ff0a600355600660ff0a60ff0a60045560066101010a60ff0a60055560066101000a6101010a600655600660ff0a6101010a60075560066101010a6101010a600855"
            ),
        )
        # check storage
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x03)),
            0x1948059DE1DEF03C4EC35FC22C2BB8F2BF45DC33085514FF7F00000000000001,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x04)),
            0x41F818A8E24EB6D7BB7B193B4F2B5FDCF4BD0D453F2AC3499D8830D391FA00FF,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x05)),
            0xEDE6FE4A943DFB5D967A2B85D6728759D40D2EF0AE4BC28BBB1867F98C0600FF,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x06)),
            0x083C936CBAAD5DE592BADC2E142FE4EBD6103921F7AA6AFF8100000000000001,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x07)),
            0x57385019FE4E0939CA3F35C37CADFAF52FBA5B1CDFB02DEF3866E8068BFA0101,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x08)),
            0x810AC878BD98428F6BE8C6426BA9F9DA09E3E33BF4FE10BFA3F8B12C92060101,
        )
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
        self.assertEqual(solve(world.current_vm.gas), 864022)

    def test_expPowerOf256_3(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: expPowerOf256_3.json
        sha256sum: 2c543fb689ceca51c0b1980c806fa2e810213ac3344812bf44b9f647ea68aa74
        Code:     PUSH1 0x3
                  PUSH2 0x100
                  EXP
                  PUSH1 0x0
                  SSTORE
                  PUSH1 0x3
                  PUSH1 0xff
                  EXP
                  PUSH1 0x1
                  SSTORE
                  PUSH1 0x3
                  PUSH2 0x101
                  EXP
                  PUSH1 0x2
                  SSTORE
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
        acc_code = unhexlify("60036101000a600055600360ff0a60015560036101010a600255")
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F2947DEF4CF144679DA39C4C32BDC35681
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

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 0)
        self.assertEqual(
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 1000000000000000000
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6),
            unhexlify("60036101000a600055600360ff0a60015560036101010a600255"),
        )
        # check storage
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x00)),
            0x01000000,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x01)), 0xFD02FF
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x02)),
            0x01030301,
        )
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
        self.assertEqual(solve(world.current_vm.gas), 39913)

    def test_mul3(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: mul3.json
        sha256sum: 9af8c2dcaaf217f7d2cbeaf72d910ae893924a3dbc4951b85404a5f050a90784
        Code:     PUSH1 0x1
                  PUSH1 0x17
                  MUL
                  PUSH1 0x0
                  SSTORE
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
        acc_code = unhexlify("6001601702600055")
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F2947DEF4CF144679DA39C4C32BDC35681
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

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 0)
        self.assertEqual(
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 1000000000000000000
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6), unhexlify("6001601702600055")
        )
        # check storage
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x00)), 0x17
        )
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
        self.assertEqual(solve(world.current_vm.gas), 79986)

    def test_expPowerOf2_256(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: expPowerOf2_256.json
        sha256sum: 5b5b5e2fdf3149601d208e55b5a19c527a74f554b7024514a5a14c10a827021b
        Code:     PUSH2 0x100
                  PUSH1 0x2
                  EXP
                  PUSH1 0x0
                  SSTORE
                  PUSH1 0xff
                  PUSH1 0x2
                  EXP
                  PUSH1 0x1
                  SSTORE
                  PUSH2 0x101
                  PUSH1 0x2
                  EXP
                  PUSH1 0x2
                  SSTORE
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
        acc_code = unhexlify("61010060020a60005560ff60020a60015561010160020a600255")
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F2947DEF4CF144679DA39C4C32BDC35681
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

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 0)
        self.assertEqual(
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 1000000000000000000
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6),
            unhexlify("61010060020a60005560ff60020a60015561010160020a600255"),
        )
        # check storage
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x01)),
            0x8000000000000000000000000000000000000000000000000000000000000000,
        )
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
        self.assertEqual(solve(world.current_vm.gas), 69893)

    def test_addmodDivByZero1(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: addmodDivByZero1.json
        sha256sum: cb6142b733dd0a41e5e83b98921b62dbed0c90e28da43109e7189cc37e20bc9d
        Code:     PUSH1 0x0
                  PUSH1 0x1
                  PUSH1 0x0
                  ADDMOD
                  PUSH1 0x0
                  SSTORE
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
        acc_code = unhexlify("60006001600008600055")
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F2947DEF4CF144679DA39C4C32BDC35681
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

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 0)
        self.assertEqual(
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 1000000000000000000
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6),
            unhexlify("60006001600008600055"),
        )
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
        self.assertEqual(solve(world.current_vm.gas), 94980)

    def test_expPowerOf256_21(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: expPowerOf256_21.json
        sha256sum: abd10e17d688e09619790af67c0553c0fafb05374496c5dcac20c86635771fd3
        Code:     PUSH1 0x15
                  PUSH2 0x100
                  EXP
                  PUSH1 0x0
                  SSTORE
                  PUSH1 0x15
                  PUSH1 0xff
                  EXP
                  PUSH1 0x1
                  SSTORE
                  PUSH1 0x15
                  PUSH2 0x101
                  EXP
                  PUSH1 0x2
                  SSTORE
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
        acc_code = unhexlify("60156101000a600055601560ff0a60015560156101010a600255")
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F2947DEF4CF144679DA39C4C32BDC35681
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

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 0)
        self.assertEqual(
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 1000000000000000000
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6),
            unhexlify("60156101000a600055601560ff0a60015560156101010a600255"),
        )
        # check storage
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x00)),
            0x01000000000000000000000000000000000000000000,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x01)),
            0xEBCCE5125534DE6B326EAD10E3645765A4312E14FF,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x02)),
            0x0115D749B152C1576391324B46A90C47946632D21501,
        )
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
        self.assertEqual(solve(world.current_vm.gas), 39913)

    def test_expPowerOf256Of256_18(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: expPowerOf256Of256_18.json
        sha256sum: 92315d900d6b1495846bfd4e53af140385e883a2af0aa67fd43a3df3a73a189e
        Code:     PUSH1 0x12
                  PUSH2 0x100
                  EXP
                  PUSH2 0x100
                  EXP
                  PUSH1 0x0
                  SSTORE
                  PUSH1 0x12
                  PUSH1 0xff
                  EXP
                  PUSH2 0x100
                  EXP
                  PUSH1 0x1
                  SSTORE
                  PUSH1 0x12
                  PUSH2 0x101
                  EXP
                  PUSH2 0x100
                  EXP
                  PUSH1 0x2
                  SSTORE
                  PUSH1 0x12
                  PUSH2 0x100
                  EXP
                  PUSH1 0xff
                  EXP
                  PUSH1 0x3
                  SSTORE
                  PUSH1 0x12
                  PUSH1 0xff
                  EXP
                  PUSH1 0xff
                  EXP
                  PUSH1 0x4
                  SSTORE
                  PUSH1 0x12
                  PUSH2 0x101
                  EXP
                  PUSH1 0xff
                  EXP
                  PUSH1 0x5
                  SSTORE
                  PUSH1 0x12
                  PUSH2 0x100
                  EXP
                  PUSH2 0x101
                  EXP
                  PUSH1 0x6
                  SSTORE
                  PUSH1 0x12
                  PUSH1 0xff
                  EXP
                  PUSH2 0x101
                  EXP
                  PUSH1 0x7
                  SSTORE
                  PUSH1 0x12
                  PUSH2 0x101
                  EXP
                  PUSH2 0x101
                  EXP
                  PUSH1 0x8
                  SSTORE
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
        gaslimit = 10000000
        world = evm.EVMWorld(
            constraints,
            blocknumber=blocknumber,
            timestamp=timestamp,
            difficulty=difficulty,
            coinbase=coinbase,
            gaslimit=gaslimit,
        )

        acc_addr = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        acc_code = unhexlify(
            "60126101000a6101000a600055601260ff0a6101000a60015560126101010a6101000a60025560126101000a60ff0a600355601260ff0a60ff0a60045560126101010a60ff0a60055560126101000a6101010a600655601260ff0a6101010a60075560126101010a6101010a600855"
        )
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F2947DEF4CF144679DA39C4C32BDC35681
        price = 0x5AF3107A4000
        value = 1000000000000000000
        gas = 1000000
        data = ""
        # open a fake tx, no funds send
        world._open_transaction("CALL", address, price, data, caller, value, gas=gas)

        # This variable might seem redundant in some tests - don't forget it is auto generated
        # and there are cases in which we need it ;)
        result, returndata = self._test_run(world)

        # World sanity checks - those should not change, right?
        self.assertEqual(solve(world.block_number()), 0)
        self.assertEqual(solve(world.block_gaslimit()), 10000000)
        self.assertEqual(solve(world.block_timestamp()), 1)
        self.assertEqual(solve(world.block_difficulty()), 256)
        self.assertEqual(solve(world.block_coinbase()), 0x2ADC25665018AA1FE0E6BC666DAC8FC2697FF9BA)

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 0)
        self.assertEqual(
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 1000000000000000000
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6),
            unhexlify(
                "60126101000a6101000a600055601260ff0a6101000a60015560126101010a6101000a60025560126101000a60ff0a600355601260ff0a60ff0a60045560126101010a60ff0a60055560126101000a6101010a600655601260ff0a6101010a60075560126101010a6101010a600855"
            ),
        )
        # check storage
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x03)),
            0x698218879EC55C33085514FF7F00000000000000000000000000000000000001,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x04)),
            0x8A2CBD9F40794E2205B13306F2AA0A43C60823C64B95D8601FA4F1E521EE00FF,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x05)),
            0xC1B5A1E3A81DA51B10D84E880F0113FF67B863DDAD3FAF1F4ECF413F101200FF,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x06)),
            0xC9B0F000B68FB921F7AA6AFF8100000000000000000000000000000000000001,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x07)),
            0x410BE68E49452A1FBCD863BF6E8D637F8EAE4979C34C88D552AFBCC20FEE0101,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x08)),
            0xF540CB714754B5B1EB0373833833BD7FB0EE925CE8B92962500B7A1C22120101,
        )
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
        self.assertEqual(solve(world.current_vm.gas), 862942)

    def test_expPowerOf256_18(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: expPowerOf256_18.json
        sha256sum: aa7f8d1062b77e9369aac793e914383284edf1024510633984f90254ce34ede5
        Code:     PUSH1 0x12
                  PUSH2 0x100
                  EXP
                  PUSH1 0x0
                  SSTORE
                  PUSH1 0x12
                  PUSH1 0xff
                  EXP
                  PUSH1 0x1
                  SSTORE
                  PUSH1 0x12
                  PUSH2 0x101
                  EXP
                  PUSH1 0x2
                  SSTORE
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
        acc_code = unhexlify("60126101000a600055601260ff0a60015560126101010a600255")
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F2947DEF4CF144679DA39C4C32BDC35681
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

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 0)
        self.assertEqual(
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 1000000000000000000
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6),
            unhexlify("60126101000a600055601260ff0a60015560126101010a600255"),
        )
        # check storage
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x00)),
            0x01000000000000000000000000000000000000,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x01)),
            0xEE95DBD2D0085A30BE71F86293F0D098EE01,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x02)),
            0x01129C3C15C100FBAC976A98A583F730991201,
        )
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
        self.assertEqual(solve(world.current_vm.gas), 39913)

    def test_smod7(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: smod7.json
        sha256sum: f994b29e003918f15520608025e571d08363b39a2f028a5c1ab6cc9121484c01
        Code:     PUSH32 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
                  PUSH32 0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
                  PUSH1 0x0
                  SUB
                  SMOD
                  PUSH1 0x0
                  SSTORE
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
        acc_code = unhexlify(
            "7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7f7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff60000307600055"
        )
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F2947DEF4CF144679DA39C4C32BDC35681
        price = 0x5AF3107A4000
        value = 1000000000000000000
        gas = 10000
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

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 0)
        self.assertEqual(
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 1000000000000000000
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6),
            unhexlify(
                "7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7f7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff60000307600055"
            ),
        )
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
        self.assertEqual(solve(world.current_vm.gas), 4980)

    def test_expPowerOf256Of256_19(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: expPowerOf256Of256_19.json
        sha256sum: 8e1ed67aa333e3b13521661a5a9e26d3580d9631301e1c2e9dd57b8cbf391699
        Code:     PUSH1 0x13
                  PUSH2 0x100
                  EXP
                  PUSH2 0x100
                  EXP
                  PUSH1 0x0
                  SSTORE
                  PUSH1 0x13
                  PUSH1 0xff
                  EXP
                  PUSH2 0x100
                  EXP
                  PUSH1 0x1
                  SSTORE
                  PUSH1 0x13
                  PUSH2 0x101
                  EXP
                  PUSH2 0x100
                  EXP
                  PUSH1 0x2
                  SSTORE
                  PUSH1 0x13
                  PUSH2 0x100
                  EXP
                  PUSH1 0xff
                  EXP
                  PUSH1 0x3
                  SSTORE
                  PUSH1 0x13
                  PUSH1 0xff
                  EXP
                  PUSH1 0xff
                  EXP
                  PUSH1 0x4
                  SSTORE
                  PUSH1 0x13
                  PUSH2 0x101
                  EXP
                  PUSH1 0xff
                  EXP
                  PUSH1 0x5
                  SSTORE
                  PUSH1 0x13
                  PUSH2 0x100
                  EXP
                  PUSH2 0x101
                  EXP
                  PUSH1 0x6
                  SSTORE
                  PUSH1 0x13
                  PUSH1 0xff
                  EXP
                  PUSH2 0x101
                  EXP
                  PUSH1 0x7
                  SSTORE
                  PUSH1 0x13
                  PUSH2 0x101
                  EXP
                  PUSH2 0x101
                  EXP
                  PUSH1 0x8
                  SSTORE
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
        gaslimit = 10000000
        world = evm.EVMWorld(
            constraints,
            blocknumber=blocknumber,
            timestamp=timestamp,
            difficulty=difficulty,
            coinbase=coinbase,
            gaslimit=gaslimit,
        )

        acc_addr = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        acc_code = unhexlify(
            "60136101000a6101000a600055601360ff0a6101000a60015560136101010a6101000a60025560136101000a60ff0a600355601360ff0a60ff0a60045560136101010a60ff0a60055560136101000a6101010a600655601360ff0a6101010a60075560136101010a6101010a600855"
        )
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F2947DEF4CF144679DA39C4C32BDC35681
        price = 0x5AF3107A4000
        value = 1000000000000000000
        gas = 1000000
        data = ""
        # open a fake tx, no funds send
        world._open_transaction("CALL", address, price, data, caller, value, gas=gas)

        # This variable might seem redundant in some tests - don't forget it is auto generated
        # and there are cases in which we need it ;)
        result, returndata = self._test_run(world)

        # World sanity checks - those should not change, right?
        self.assertEqual(solve(world.block_number()), 0)
        self.assertEqual(solve(world.block_gaslimit()), 10000000)
        self.assertEqual(solve(world.block_timestamp()), 1)
        self.assertEqual(solve(world.block_difficulty()), 256)
        self.assertEqual(solve(world.block_coinbase()), 0x2ADC25665018AA1FE0E6BC666DAC8FC2697FF9BA)

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 0)
        self.assertEqual(
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 1000000000000000000
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6),
            unhexlify(
                "60136101000a6101000a600055601360ff0a6101000a60015560136101010a6101000a60025560136101000a60ff0a600355601360ff0a60ff0a60045560136101010a60ff0a60055560136101000a6101010a600655601360ff0a6101010a60075560136101010a6101010a600855"
            ),
        )
        # check storage
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x03)),
            0x8218879EC55C33085514FF7F0000000000000000000000000000000000000001,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x04)),
            0xB795AD7AC24CFBB7435CF53BD3584F3D4B2709935635C3CEB66E761FF091FEFF,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x05)),
            0x1F0BB7BE91A0CCD0CCA93D75CF03DE3E6B56FE8F1C54242617665327219300FF,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x06)),
            0xB0F000B68FB921F7AA6AFF810000000000000000000000000000000000000001,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x07)),
            0xAD571756ECBFF1BFDEF064861E5E92C5D897A9CC380E54BDBAABD80BB793FF01,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x08)),
            0xD8B5B531989E689F700DCDB43AB90E79A49DFBBB5A13DBF751DF98BB34930101,
        )
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
        self.assertEqual(solve(world.current_vm.gas), 862852)

    def test_expPowerOf256Of256_3(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: expPowerOf256Of256_3.json
        sha256sum: ed99ceec8519b10c02299fa905e9822071e3457d195206d67a29dca715949fd5
        Code:     PUSH1 0x3
                  PUSH2 0x100
                  EXP
                  PUSH2 0x100
                  EXP
                  PUSH1 0x0
                  SSTORE
                  PUSH1 0x3
                  PUSH1 0xff
                  EXP
                  PUSH2 0x100
                  EXP
                  PUSH1 0x1
                  SSTORE
                  PUSH1 0x3
                  PUSH2 0x101
                  EXP
                  PUSH2 0x100
                  EXP
                  PUSH1 0x2
                  SSTORE
                  PUSH1 0x3
                  PUSH2 0x100
                  EXP
                  PUSH1 0xff
                  EXP
                  PUSH1 0x3
                  SSTORE
                  PUSH1 0x3
                  PUSH1 0xff
                  EXP
                  PUSH1 0xff
                  EXP
                  PUSH1 0x4
                  SSTORE
                  PUSH1 0x3
                  PUSH2 0x101
                  EXP
                  PUSH1 0xff
                  EXP
                  PUSH1 0x5
                  SSTORE
                  PUSH1 0x3
                  PUSH2 0x100
                  EXP
                  PUSH2 0x101
                  EXP
                  PUSH1 0x6
                  SSTORE
                  PUSH1 0x3
                  PUSH1 0xff
                  EXP
                  PUSH2 0x101
                  EXP
                  PUSH1 0x7
                  SSTORE
                  PUSH1 0x3
                  PUSH2 0x101
                  EXP
                  PUSH2 0x101
                  EXP
                  PUSH1 0x8
                  SSTORE
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
        gaslimit = 10000000
        world = evm.EVMWorld(
            constraints,
            blocknumber=blocknumber,
            timestamp=timestamp,
            difficulty=difficulty,
            coinbase=coinbase,
            gaslimit=gaslimit,
        )

        acc_addr = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        acc_code = unhexlify(
            "60036101000a6101000a600055600360ff0a6101000a60015560036101010a6101000a60025560036101000a60ff0a600355600360ff0a60ff0a60045560036101010a60ff0a60055560036101000a6101010a600655600360ff0a6101010a60075560036101010a6101010a600855"
        )
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F2947DEF4CF144679DA39C4C32BDC35681
        price = 0x5AF3107A4000
        value = 1000000000000000000
        gas = 1000000
        data = ""
        # open a fake tx, no funds send
        world._open_transaction("CALL", address, price, data, caller, value, gas=gas)

        # This variable might seem redundant in some tests - don't forget it is auto generated
        # and there are cases in which we need it ;)
        result, returndata = self._test_run(world)

        # World sanity checks - those should not change, right?
        self.assertEqual(solve(world.block_number()), 0)
        self.assertEqual(solve(world.block_gaslimit()), 10000000)
        self.assertEqual(solve(world.block_timestamp()), 1)
        self.assertEqual(solve(world.block_difficulty()), 256)
        self.assertEqual(solve(world.block_coinbase()), 0x2ADC25665018AA1FE0E6BC666DAC8FC2697FF9BA)

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 0)
        self.assertEqual(
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 1000000000000000000
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6),
            unhexlify(
                "60036101000a6101000a600055600360ff0a6101000a60015560036101010a6101000a60025560036101000a60ff0a600355600360ff0a60ff0a60045560036101010a60ff0a60055560036101000a6101010a600655600360ff0a6101010a60075560036101010a6101010a600855"
            ),
        )
        # check storage
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x03)),
            0x109A00E1370D2D2922BF892E85BECB54297354B2E5C75388D514FF7F00000001,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x04)),
            0x54A792F15E9ABA7E4AD9E716BC169EEA3A6E2E9C49BF9B335874613C8081FEFF,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x05)),
            0x5D24A14D8E5E039372CD0F6A0F31E9ED6B75ADBA9F16B1C5B3EDD5BA818300FF,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x06)),
            0x298E2F316B4CCDED5EBF515998D9EC20DF69404B04A441782A6AFF8100000001,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x07)),
            0x4335694E98F372183C62A2339FA4AD161E9B4C42240BDC9452ABFFD07783FF01,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x08)),
            0xF0F0820797315ACD063056BBA76F6A9C3E281CDB5197A233967CA94684830101,
        )
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
        self.assertEqual(solve(world.current_vm.gas), 864292)

    def test_smod5(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: smod5.json
        sha256sum: 7d01d4c43ccc6c8229f960244f07169118613c9a3d6112a1b602695f4c6d3132
        Code:     PUSH32 0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
                  PUSH32 0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
                  PUSH1 0x0
                  SUB
                  SMOD
                  PUSH1 0x0
                  SSTORE
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
        acc_code = unhexlify(
            "7f7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7f7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff60000307600055"
        )
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F2947DEF4CF144679DA39C4C32BDC35681
        price = 0x5AF3107A4000
        value = 1000000000000000000
        gas = 10000
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

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 0)
        self.assertEqual(
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 1000000000000000000
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6),
            unhexlify(
                "7f7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7f7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff60000307600055"
            ),
        )
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
        self.assertEqual(solve(world.current_vm.gas), 4980)

    def test_expPowerOf256Of256_16(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: expPowerOf256Of256_16.json
        sha256sum: 5acb81a90afe62bab2a068d166ab7e0d77fdf71db887357486eaa57be2097585
        Code:     PUSH1 0x10
                  PUSH2 0x100
                  EXP
                  PUSH2 0x100
                  EXP
                  PUSH1 0x0
                  SSTORE
                  PUSH1 0x10
                  PUSH1 0xff
                  EXP
                  PUSH2 0x100
                  EXP
                  PUSH1 0x1
                  SSTORE
                  PUSH1 0x10
                  PUSH2 0x101
                  EXP
                  PUSH2 0x100
                  EXP
                  PUSH1 0x2
                  SSTORE
                  PUSH1 0x10
                  PUSH2 0x100
                  EXP
                  PUSH1 0xff
                  EXP
                  PUSH1 0x3
                  SSTORE
                  PUSH1 0x10
                  PUSH1 0xff
                  EXP
                  PUSH1 0xff
                  EXP
                  PUSH1 0x4
                  SSTORE
                  PUSH1 0x10
                  PUSH2 0x101
                  EXP
                  PUSH1 0xff
                  EXP
                  PUSH1 0x5
                  SSTORE
                  PUSH1 0x10
                  PUSH2 0x100
                  EXP
                  PUSH2 0x101
                  EXP
                  PUSH1 0x6
                  SSTORE
                  PUSH1 0x10
                  PUSH1 0xff
                  EXP
                  PUSH2 0x101
                  EXP
                  PUSH1 0x7
                  SSTORE
                  PUSH1 0x10
                  PUSH2 0x101
                  EXP
                  PUSH2 0x101
                  EXP
                  PUSH1 0x8
                  SSTORE
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
        gaslimit = 10000000
        world = evm.EVMWorld(
            constraints,
            blocknumber=blocknumber,
            timestamp=timestamp,
            difficulty=difficulty,
            coinbase=coinbase,
            gaslimit=gaslimit,
        )

        acc_addr = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        acc_code = unhexlify(
            "60106101000a6101000a600055601060ff0a6101000a60015560106101010a6101000a60025560106101000a60ff0a600355601060ff0a60ff0a60045560106101010a60ff0a60055560106101000a6101010a600655601060ff0a6101010a60075560106101010a6101010a600855"
        )
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F2947DEF4CF144679DA39C4C32BDC35681
        price = 0x5AF3107A4000
        value = 1000000000000000000
        gas = 1000000
        data = ""
        # open a fake tx, no funds send
        world._open_transaction("CALL", address, price, data, caller, value, gas=gas)

        # This variable might seem redundant in some tests - don't forget it is auto generated
        # and there are cases in which we need it ;)
        result, returndata = self._test_run(world)

        # World sanity checks - those should not change, right?
        self.assertEqual(solve(world.block_number()), 0)
        self.assertEqual(solve(world.block_gaslimit()), 10000000)
        self.assertEqual(solve(world.block_timestamp()), 1)
        self.assertEqual(solve(world.block_difficulty()), 256)
        self.assertEqual(solve(world.block_coinbase()), 0x2ADC25665018AA1FE0E6BC666DAC8FC2697FF9BA)

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 0)
        self.assertEqual(
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 1000000000000000000
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6),
            unhexlify(
                "60106101000a6101000a600055601060ff0a6101000a60015560106101010a6101000a60025560106101000a60ff0a600355601060ff0a60ff0a60045560106101010a60ff0a60055560106101000a6101010a600655601060ff0a6101010a60075560106101010a6101010a600855"
            ),
        )
        # check storage
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x03)),
            0x82EC698218879EC55C33085514FF7F0000000000000000000000000000000001,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x04)),
            0x3122F4BCDF6DD8B265CD18EB6AF28C879AED44A35E0BF59273E39E6C7FF000FF,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x05)),
            0x6A2B3BC87A02C29B9D27757DF43047ECD0F15485270FCA27417A701C701000FF,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x06)),
            0x228FC9B0F000B68FB921F7AA6AFF810000000000000000000000000000000001,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x07)),
            0x88E1259502EEF93D46060AACC9E2FF506C734DADE0B6714AB12D17E46FF00101,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x08)),
            0x4A103813C12C12169B218296BB0A9EAE80CF8D2B158AA70EB990F99480100101,
        )
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
        self.assertEqual(solve(world.current_vm.gas), 863122)

    def test_exp3(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: exp3.json
        sha256sum: 30aff2bd2353be208e4964a24a76d95d6c5e8d4c272189219c821ab7f4aae95d
        Code:     PUSH4 0x7fffffff
                  PUSH1 0x0
                  EXP
                  PUSH1 0x0
                  SSTORE
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
        acc_code = unhexlify("637fffffff60000a600055")
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F2947DEF4CF144679DA39C4C32BDC35681
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

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 0)
        self.assertEqual(
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 1000000000000000000
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6),
            unhexlify("637fffffff60000a600055"),
        )
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
        self.assertEqual(solve(world.current_vm.gas), 94941)

    def test_mulmod3_0(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: mulmod3_0.json
        sha256sum: a2408325f3e9c8d5154f3c1d8d19adaad67222e2f5032350e6cee4ff7f9124c5
        Code:     PUSH1 0x2
                  PUSH1 0x3
                  PUSH1 0x0
                  SUB
                  PUSH1 0x1
                  PUSH1 0x5
                  MULMOD
                  EQ
                  PUSH1 0x0
                  SSTORE
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
        acc_code = unhexlify("60026003600003600160050914600055")
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F2947DEF4CF144679DA39C4C32BDC35681
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

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 0)
        self.assertEqual(
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 1000000000000000000
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6),
            unhexlify("60026003600003600160050914600055"),
        )
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
        self.assertEqual(solve(world.current_vm.gas), 94968)

    def test_expPowerOf2_64(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: expPowerOf2_64.json
        sha256sum: 0a917c261c69f13064e5ca6c65b8f3fa61ee9013526b33ae828887b0605b8d0f
        Code:     PUSH1 0x40
                  PUSH1 0x2
                  EXP
                  PUSH1 0x0
                  SSTORE
                  PUSH1 0x3f
                  PUSH1 0x2
                  EXP
                  PUSH1 0x1
                  SSTORE
                  PUSH1 0x41
                  PUSH1 0x2
                  EXP
                  PUSH1 0x2
                  SSTORE
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
        acc_code = unhexlify("604060020a600055603f60020a600155604160020a600255")
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F2947DEF4CF144679DA39C4C32BDC35681
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

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 0)
        self.assertEqual(
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 1000000000000000000
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6),
            unhexlify("604060020a600055603f60020a600155604160020a600255"),
        )
        # check storage
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x00)),
            0x010000000000000000,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x01)),
            0x8000000000000000,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x02)),
            0x020000000000000000,
        )
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
        self.assertEqual(solve(world.current_vm.gas), 39913)

    def test_sdiv_i256min(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: sdiv_i256min.json
        sha256sum: a75f354304eea0930d85934b46916213c26a7c3b17905786de6ce0d75e8b9cf0
        Code:     PUSH1 0x1
                  PUSH1 0x0
                  SUB
                  PUSH32 0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
                  PUSH1 0x0
                  SUB
                  SDIV
                  PUSH1 0x0
                  SSTORE
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
        acc_code = unhexlify(
            "60016000037f7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff60000305600055"
        )
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F2947DEF4CF144679DA39C4C32BDC35681
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

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 0)
        self.assertEqual(
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 1000000000000000000
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6),
            unhexlify(
                "60016000037f7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff60000305600055"
            ),
        )
        # check storage
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x00)),
            0x7FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF,
        )
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
        self.assertEqual(solve(world.current_vm.gas), 79974)

    def test_signextend_AlmostBiggestByte(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: signextend_AlmostBiggestByte.json
        sha256sum: 9e580dec6eab6488b54f744e2622c6062312b1219c08e29b8b476d05bf0891d5
        Code:     PUSH32 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe
                  PUSH32 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe
                  SIGNEXTEND
                  PUSH1 0x0
                  SSTORE
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
        gaslimit = 10000000
        world = evm.EVMWorld(
            constraints,
            blocknumber=blocknumber,
            timestamp=timestamp,
            difficulty=difficulty,
            coinbase=coinbase,
            gaslimit=gaslimit,
        )

        acc_addr = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        acc_code = unhexlify(
            "7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0b600055"
        )
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F2947DEF4CF144679DA39C4C32BDC35681
        price = 0x5AF3107A4000
        value = 1000000000000000000
        gas = 1000000
        data = ""
        # open a fake tx, no funds send
        world._open_transaction("CALL", address, price, data, caller, value, gas=gas)

        # This variable might seem redundant in some tests - don't forget it is auto generated
        # and there are cases in which we need it ;)
        result, returndata = self._test_run(world)

        # World sanity checks - those should not change, right?
        self.assertEqual(solve(world.block_number()), 0)
        self.assertEqual(solve(world.block_gaslimit()), 10000000)
        self.assertEqual(solve(world.block_timestamp()), 1)
        self.assertEqual(solve(world.block_difficulty()), 256)
        self.assertEqual(solve(world.block_coinbase()), 0x2ADC25665018AA1FE0E6BC666DAC8FC2697FF9BA)

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 0)
        self.assertEqual(
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 1000000000000000000
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6),
            unhexlify(
                "7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0b600055"
            ),
        )
        # check storage
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x00)),
            0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFE,
        )
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
        self.assertEqual(solve(world.current_vm.gas), 979986)

    def test_sdivByZero0(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: sdivByZero0.json
        sha256sum: d6e23171cfe8625fb39ce7d15d8b72776b0c2854017aadeff0bc2458983a76d1
        Code:     PUSH1 0x0
                  PUSH1 0x0
                  SUB
                  PUSH1 0x3
                  PUSH1 0x0
                  SUB
                  SDIV
                  PUSH1 0x0
                  SSTORE
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
        acc_code = unhexlify("6000600003600360000305600055")
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F2947DEF4CF144679DA39C4C32BDC35681
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

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 0)
        self.assertEqual(
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 1000000000000000000
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6),
            unhexlify("6000600003600360000305600055"),
        )
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
        self.assertEqual(solve(world.current_vm.gas), 94974)

    def test_mulmoddivByZero1(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: mulmoddivByZero1.json
        sha256sum: cf49980ff3395877d56a96edcf18b1e369b68c5d06822e8327f1c3f2ee27aa1e
        Code:     PUSH1 0x0
                  PUSH1 0x1
                  PUSH1 0x0
                  MULMOD
                  PUSH1 0x0
                  SSTORE
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
        acc_code = unhexlify("60006001600009600055")
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F2947DEF4CF144679DA39C4C32BDC35681
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

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 0)
        self.assertEqual(
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 1000000000000000000
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6),
            unhexlify("60006001600009600055"),
        )
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
        self.assertEqual(solve(world.current_vm.gas), 94980)

    def test_expPowerOf2_128(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: expPowerOf2_128.json
        sha256sum: d769c6a75d99975be8e86784d56d45d33ff36eeba52f7a238daa12e84ffa854b
        Code:     PUSH1 0x80
                  PUSH1 0x2
                  EXP
                  PUSH1 0x0
                  SSTORE
                  PUSH1 0x7f
                  PUSH1 0x2
                  EXP
                  PUSH1 0x1
                  SSTORE
                  PUSH1 0x81
                  PUSH1 0x2
                  EXP
                  PUSH1 0x2
                  SSTORE
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
        acc_code = unhexlify("608060020a600055607f60020a600155608160020a600255")
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F2947DEF4CF144679DA39C4C32BDC35681
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

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 0)
        self.assertEqual(
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 1000000000000000000
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6),
            unhexlify("608060020a600055607f60020a600155608160020a600255"),
        )
        # check storage
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x00)),
            0x0100000000000000000000000000000000,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x01)),
            0x80000000000000000000000000000000,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x02)),
            0x0200000000000000000000000000000000,
        )
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
        self.assertEqual(solve(world.current_vm.gas), 39913)

    def test_mul1(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: mul1.json
        sha256sum: c27023f53c812b9cbb868e7f76fc946c62869666668f44cf8fa85660c373d01d
        Code:     PUSH32 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
                  PUSH32 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
                  MUL
                  PUSH1 0x0
                  SSTORE
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
        acc_code = unhexlify(
            "7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff02600055"
        )
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F2947DEF4CF144679DA39C4C32BDC35681
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

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 0)
        self.assertEqual(
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 1000000000000000000
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6),
            unhexlify(
                "7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff02600055"
            ),
        )
        # check storage
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x00)), 0x01
        )
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
        self.assertEqual(solve(world.current_vm.gas), 79986)

    def test_exp1(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: exp1.json
        sha256sum: 2d558bca9c3748e933bf10ae3ed17cb8a9ffbaf12afbe5d03e56ec266ea7842c
        Code:     PUSH32 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe
                  PUSH32 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
                  EXP
                  PUSH1 0x0
                  SSTORE
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
        acc_code = unhexlify(
            "7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0a600055"
        )
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F2947DEF4CF144679DA39C4C32BDC35681
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

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 0)
        self.assertEqual(
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 1000000000000000000
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6),
            unhexlify(
                "7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0a600055"
            ),
        )
        # check storage
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x00)), 0x01
        )
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
        self.assertEqual(solve(world.current_vm.gas), 79661)

    def test_expPowerOf256Of256_8(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: expPowerOf256Of256_8.json
        sha256sum: 670bc5532f9085f0b0ba382e693a5b57ce1674ec3c25cabef57cb97fd5b41962
        Code:     PUSH1 0x8
                  PUSH2 0x100
                  EXP
                  PUSH2 0x100
                  EXP
                  PUSH1 0x0
                  SSTORE
                  PUSH1 0x8
                  PUSH1 0xff
                  EXP
                  PUSH2 0x100
                  EXP
                  PUSH1 0x1
                  SSTORE
                  PUSH1 0x8
                  PUSH2 0x101
                  EXP
                  PUSH2 0x100
                  EXP
                  PUSH1 0x2
                  SSTORE
                  PUSH1 0x8
                  PUSH2 0x100
                  EXP
                  PUSH1 0xff
                  EXP
                  PUSH1 0x3
                  SSTORE
                  PUSH1 0x8
                  PUSH1 0xff
                  EXP
                  PUSH1 0xff
                  EXP
                  PUSH1 0x4
                  SSTORE
                  PUSH1 0x8
                  PUSH2 0x101
                  EXP
                  PUSH1 0xff
                  EXP
                  PUSH1 0x5
                  SSTORE
                  PUSH1 0x8
                  PUSH2 0x100
                  EXP
                  PUSH2 0x101
                  EXP
                  PUSH1 0x6
                  SSTORE
                  PUSH1 0x8
                  PUSH1 0xff
                  EXP
                  PUSH2 0x101
                  EXP
                  PUSH1 0x7
                  SSTORE
                  PUSH1 0x8
                  PUSH2 0x101
                  EXP
                  PUSH2 0x101
                  EXP
                  PUSH1 0x8
                  SSTORE
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
        gaslimit = 100000000
        world = evm.EVMWorld(
            constraints,
            blocknumber=blocknumber,
            timestamp=timestamp,
            difficulty=difficulty,
            coinbase=coinbase,
            gaslimit=gaslimit,
        )

        acc_addr = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        acc_code = unhexlify(
            "60086101000a6101000a600055600860ff0a6101000a60015560086101010a6101000a60025560086101000a60ff0a600355600860ff0a60ff0a60045560086101010a60ff0a60055560086101000a6101010a600655600860ff0a6101010a60075560086101010a6101010a600855"
        )
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F2947DEF4CF144679DA39C4C32BDC35681
        price = 0x5AF3107A4000
        value = 1000000000000000000
        gas = 10000000
        data = ""
        # open a fake tx, no funds send
        world._open_transaction("CALL", address, price, data, caller, value, gas=gas)

        # This variable might seem redundant in some tests - don't forget it is auto generated
        # and there are cases in which we need it ;)
        result, returndata = self._test_run(world)

        # World sanity checks - those should not change, right?
        self.assertEqual(solve(world.block_number()), 0)
        self.assertEqual(solve(world.block_gaslimit()), 100000000)
        self.assertEqual(solve(world.block_timestamp()), 1)
        self.assertEqual(solve(world.block_difficulty()), 256)
        self.assertEqual(solve(world.block_coinbase()), 0x2ADC25665018AA1FE0E6BC666DAC8FC2697FF9BA)

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 0)
        self.assertEqual(
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 1000000000000000000
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6),
            unhexlify(
                "60086101000a6101000a600055600860ff0a6101000a60015560086101010a6101000a60025560086101000a60ff0a600355600860ff0a60ff0a60045560086101010a60ff0a60055560086101000a6101010a600655600860ff0a6101010a60075560086101010a6101010a600855"
            ),
        )
        # check storage
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x03)),
            0x230041A0E7602D6E459609ED39081EC55C33085514FF7F000000000000000001,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x04)),
            0xC407D8A413EF9079EAD457ED686A05AC81039C0CAE0A7F6AFD01E8461FF800FF,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x05)),
            0x67A397E0692385E4CD83853AABCE220A94D449E885FA867E96D3EF5E180800FF,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x06)),
            0x70ADD926E753655D6D0EBE9C0F81368FB921F7AA6AFF81000000000000000001,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x07)),
            0x0BDCE80B8378E43F13D454B9D0A4C83CF311B8EAA45D5122CFD544A217F80101,
        )
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x08)),
            0x629C25790E1488998877A9ECDF0FB69637E77D8A4BDC1B46270093BA20080101,
        )
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
        self.assertEqual(solve(world.current_vm.gas), 9863842)

    def test_signextend_BitIsNotSet(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: signextend_BitIsNotSet.json
        sha256sum: 3e15e2e67dbe83ccdcf1eee546bff42a1eeb19ca892a0fb6610002cefc5c0440
        Code:     PUSH3 0x122f6a
                  PUSH1 0x0
                  SIGNEXTEND
                  PUSH1 0x0
                  SSTORE
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
        gaslimit = 10000000
        world = evm.EVMWorld(
            constraints,
            blocknumber=blocknumber,
            timestamp=timestamp,
            difficulty=difficulty,
            coinbase=coinbase,
            gaslimit=gaslimit,
        )

        acc_addr = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        acc_code = unhexlify("62122f6a60000b600055")
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F2947DEF4CF144679DA39C4C32BDC35681
        price = 0x5AF3107A4000
        value = 1000000000000000000
        gas = 1000000
        data = ""
        # open a fake tx, no funds send
        world._open_transaction("CALL", address, price, data, caller, value, gas=gas)

        # This variable might seem redundant in some tests - don't forget it is auto generated
        # and there are cases in which we need it ;)
        result, returndata = self._test_run(world)

        # World sanity checks - those should not change, right?
        self.assertEqual(solve(world.block_number()), 0)
        self.assertEqual(solve(world.block_gaslimit()), 10000000)
        self.assertEqual(solve(world.block_timestamp()), 1)
        self.assertEqual(solve(world.block_difficulty()), 256)
        self.assertEqual(solve(world.block_coinbase()), 0x2ADC25665018AA1FE0E6BC666DAC8FC2697FF9BA)

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 0)
        self.assertEqual(
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 1000000000000000000
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6),
            unhexlify("62122f6a60000b600055"),
        )
        # check storage
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x00)), 0x6A
        )
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
        self.assertEqual(solve(world.current_vm.gas), 979986)

    def test_smod4(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: smod4.json
        sha256sum: 82200247a72e367fa74d3a2b2d11ebe126ee2c51861b79bc30f793010118e88c
        Code:     PUSH1 0x0
                  PUSH1 0x2
                  PUSH1 0x0
                  SUB
                  SMOD
                  PUSH1 0x0
                  SSTORE
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
        acc_code = unhexlify("6000600260000307600055")
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F2947DEF4CF144679DA39C4C32BDC35681
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

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 0)
        self.assertEqual(
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 1000000000000000000
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6),
            unhexlify("6000600260000307600055"),
        )
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
        self.assertEqual(solve(world.current_vm.gas), 94980)

    def test_divByNonZero1(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: divByNonZero1.json
        sha256sum: e9aae6886ceb4107c9b254a1764a4560c32ab4097cbb4b8ebd6aa8dddf20e3de
        Code:     PUSH1 0x18
                  PUSH1 0x17
                  DIV
                  PUSH1 0x0
                  SSTORE
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
        acc_code = unhexlify("6018601704600055")
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F2947DEF4CF144679DA39C4C32BDC35681
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

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 0)
        self.assertEqual(
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 1000000000000000000
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6), unhexlify("6018601704600055")
        )
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
        self.assertEqual(solve(world.current_vm.gas), 94986)

    def test_exp6(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: exp6.json
        sha256sum: 857a587c2ec9246189d9d0f9837c05d5b71f878d15635b59187d5cb63e1db3c7
        Code:     PUSH2 0x101
                  PUSH1 0x1
                  EXP
                  PUSH1 0x0
                  SSTORE
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
        acc_code = unhexlify("61010160010a600055")
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F2947DEF4CF144679DA39C4C32BDC35681
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

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 0)
        self.assertEqual(
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 1000000000000000000
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6),
            unhexlify("61010160010a600055"),
        )
        # check storage
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x00)), 0x01
        )
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
        self.assertEqual(solve(world.current_vm.gas), 79961)

    def test_divByNonZero0(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: divByNonZero0.json
        sha256sum: e4f4a0965d214b1ac34b98e22b3098d9574518d7e0f62916606aa70180f08b0b
        Code:     PUSH1 0x2
                  PUSH1 0x5
                  DIV
                  PUSH1 0x0
                  SSTORE
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
        acc_code = unhexlify("6002600504600055")
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F2947DEF4CF144679DA39C4C32BDC35681
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

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 0)
        self.assertEqual(
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 1000000000000000000
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6), unhexlify("6002600504600055")
        )
        # check storage
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x00)), 0x02
        )
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
        self.assertEqual(solve(world.current_vm.gas), 79986)

    def test_addmod1(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: addmod1.json
        sha256sum: 9e7cb74d28005ca4b84e66485c95a896c62a3605a453e37eb15e287c8be7d942
        Code:     PUSH1 0x2
                  PUSH1 0x2
                  PUSH1 0x0
                  SUB
                  PUSH1 0x1
                  PUSH1 0x0
                  SUB
                  ADDMOD
                  PUSH1 0x0
                  SSTORE
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
        acc_code = unhexlify("60026002600003600160000308600055")
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F2947DEF4CF144679DA39C4C32BDC35681
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

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 0)
        self.assertEqual(
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)), 1000000000000000000
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6),
            unhexlify("60026002600003600160000308600055"),
        )
        # check storage
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x00)), 0x01
        )
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
        self.assertEqual(solve(world.current_vm.gas), 79968)


if __name__ == "__main__":
    unittest.main()
