"""DO NOT MODIFY: Tests generated from `VMTests/vmEnvironmentalInfo` with make_VMTests.py"""
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


class EVMTest_vmEnvironmentalInfo(unittest.TestCase):
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

    def test_calldatasize0(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: calldatasize0.json
        sha256sum: d0ca8fd60a1fb59685baa4e0aba4561b0da07be7a091108b9b67c787d337c476
        Code:     CALLDATASIZE
                  PUSH1 0x0
                  SSTORE
        """

        def solve(val):
            return self._solve(constraints, val)

        constraints = ConstraintSet()

        blocknumber = constraints.new_bitvec(256, name="blocknumber")
        constraints.add(blocknumber == 0)

        timestamp = constraints.new_bitvec(256, name="timestamp")
        constraints.add(timestamp == 1)

        difficulty = constraints.new_bitvec(256, name="difficulty")
        constraints.add(difficulty == 256)

        coinbase = constraints.new_bitvec(256, name="coinbase")
        constraints.add(coinbase == 244687034288125203496486448490407391986876152250)

        gaslimit = constraints.new_bitvec(256, name="gaslimit")
        constraints.add(gaslimit == 1000000)

        world = evm.EVMWorld(
            constraints,
            blocknumber=blocknumber,
            timestamp=timestamp,
            difficulty=difficulty,
            coinbase=coinbase,
            gaslimit=gaslimit,
        )

        acc_addr = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        acc_code = unhexlify("36600055")

        acc_balance = constraints.new_bitvec(
            256, name="balance_0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6"
        )
        constraints.add(acc_balance == 100000000000000000000000)

        acc_nonce = constraints.new_bitvec(
            256, name="nonce_0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6"
        )
        constraints.add(acc_nonce == 0)

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F3947DEF4CF144679DA39C4C32BDC35681
        price = constraints.new_bitvec(256, name="price")
        constraints.add(price == 1000000000)

        value = constraints.new_bitvec(256, name="value")
        constraints.add(value == 1000000000000000000)

        gas = constraints.new_bitvec(256, name="gas")
        constraints.add(gas == 100000000000)

        data = constraints.new_array(index_max=2)
        constraints.add(data == b"%`")

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
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)),
            100000000000000000000000,
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6), unhexlify("36600055")
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
        self.assertEqual(solve(world.current_vm.gas), 99999979995)

    def test_callvalue(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: callvalue.json
        sha256sum: 09e5c3d0625d42c6204d48503ebce4e85c601c68f1e4e48d687935dbdcc46e0a
        Code:     CALLVALUE
                  PUSH1 0x0
                  SSTORE
        """

        def solve(val):
            return self._solve(constraints, val)

        constraints = ConstraintSet()

        blocknumber = constraints.new_bitvec(256, name="blocknumber")
        constraints.add(blocknumber == 0)

        timestamp = constraints.new_bitvec(256, name="timestamp")
        constraints.add(timestamp == 1)

        difficulty = constraints.new_bitvec(256, name="difficulty")
        constraints.add(difficulty == 256)

        coinbase = constraints.new_bitvec(256, name="coinbase")
        constraints.add(coinbase == 244687034288125203496486448490407391986876152250)

        gaslimit = constraints.new_bitvec(256, name="gaslimit")
        constraints.add(gaslimit == 1000000)

        world = evm.EVMWorld(
            constraints,
            blocknumber=blocknumber,
            timestamp=timestamp,
            difficulty=difficulty,
            coinbase=coinbase,
            gaslimit=gaslimit,
        )

        acc_addr = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        acc_code = unhexlify("34600055")

        acc_balance = constraints.new_bitvec(
            256, name="balance_0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6"
        )
        constraints.add(acc_balance == 100000000000000000000000)

        acc_nonce = constraints.new_bitvec(
            256, name="nonce_0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6"
        )
        constraints.add(acc_nonce == 0)

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F3947DEF4CF144679DA39C4C32BDC35681
        price = constraints.new_bitvec(256, name="price")
        constraints.add(price == 1000000000)

        value = constraints.new_bitvec(256, name="value")
        constraints.add(value == 1000000000000000000)

        gas = constraints.new_bitvec(256, name="gas")
        constraints.add(gas == 100000000000)

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
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)),
            100000000000000000000000,
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6), unhexlify("34600055")
        )
        # check storage
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x00)),
            0x0DE0B6B3A7640000,
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
        self.assertEqual(solve(world.current_vm.gas), 99999979995)

    def test_origin(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: origin.json
        sha256sum: 3480b0e1ca40883b9fe4cf4e7a4da98614d94eb0c702beda49ccb84dbc0b2d68
        Code:     ORIGIN
                  PUSH1 0x0
                  SSTORE
        """

        def solve(val):
            return self._solve(constraints, val)

        constraints = ConstraintSet()

        blocknumber = constraints.new_bitvec(256, name="blocknumber")
        constraints.add(blocknumber == 0)

        timestamp = constraints.new_bitvec(256, name="timestamp")
        constraints.add(timestamp == 1)

        difficulty = constraints.new_bitvec(256, name="difficulty")
        constraints.add(difficulty == 256)

        coinbase = constraints.new_bitvec(256, name="coinbase")
        constraints.add(coinbase == 244687034288125203496486448490407391986876152250)

        gaslimit = constraints.new_bitvec(256, name="gaslimit")
        constraints.add(gaslimit == 1000000)

        world = evm.EVMWorld(
            constraints,
            blocknumber=blocknumber,
            timestamp=timestamp,
            difficulty=difficulty,
            coinbase=coinbase,
            gaslimit=gaslimit,
        )

        acc_addr = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        acc_code = unhexlify("32600055")

        acc_balance = constraints.new_bitvec(
            256, name="balance_0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6"
        )
        constraints.add(acc_balance == 100000000000000000000000)

        acc_nonce = constraints.new_bitvec(
            256, name="nonce_0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6"
        )
        constraints.add(acc_nonce == 0)

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F3947DEF4CF144679DA39C4C32BDC35681
        price = constraints.new_bitvec(256, name="price")
        constraints.add(price == 1000000000)

        value = constraints.new_bitvec(256, name="value")
        constraints.add(value == 1000000000000000000)

        gas = constraints.new_bitvec(256, name="gas")
        constraints.add(gas == 100000000000)

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
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)),
            100000000000000000000000,
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6), unhexlify("32600055")
        )
        # check storage
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x00)),
            0xCD1722F3947DEF4CF144679DA39C4C32BDC35681,
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
        self.assertEqual(solve(world.current_vm.gas), 99999979995)

    def test_codecopyZeroMemExpansion(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: codecopyZeroMemExpansion.json
        sha256sum: 1f5175b0b68ce027be1757ee20f17d04cfbcaa36b2241c37ff15ff419bbc5297
        Code:     PUSH1 0x0
                  PUSH1 0x0
                  PUSH1 0x0
                  CODECOPY
                  PUSH1 0x0
                  MLOAD
                  PUSH1 0x0
                  SSTORE
        """

        def solve(val):
            return self._solve(constraints, val)

        constraints = ConstraintSet()

        blocknumber = constraints.new_bitvec(256, name="blocknumber")
        constraints.add(blocknumber == 0)

        timestamp = constraints.new_bitvec(256, name="timestamp")
        constraints.add(timestamp == 1)

        difficulty = constraints.new_bitvec(256, name="difficulty")
        constraints.add(difficulty == 256)

        coinbase = constraints.new_bitvec(256, name="coinbase")
        constraints.add(coinbase == 244687034288125203496486448490407391986876152250)

        gaslimit = constraints.new_bitvec(256, name="gaslimit")
        constraints.add(gaslimit == 1000000)

        world = evm.EVMWorld(
            constraints,
            blocknumber=blocknumber,
            timestamp=timestamp,
            difficulty=difficulty,
            coinbase=coinbase,
            gaslimit=gaslimit,
        )

        acc_addr = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        acc_code = unhexlify("60006000600039600051600055")

        acc_balance = constraints.new_bitvec(
            256, name="balance_0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6"
        )
        constraints.add(acc_balance == 100000000000000000000000)

        acc_nonce = constraints.new_bitvec(
            256, name="nonce_0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6"
        )
        constraints.add(acc_nonce == 0)

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F3947DEF4CF144679DA39C4C32BDC35681
        price = constraints.new_bitvec(256, name="price")
        constraints.add(price == 1000000000)

        value = constraints.new_bitvec(256, name="value")
        constraints.add(value == 1000000000000000000)

        gas = constraints.new_bitvec(256, name="gas")
        constraints.add(gas == 100000000000)

        data = constraints.new_array(index_max=17)
        constraints.add(data == b"\x124Vx\x90\xab\xcd\xef\x01#Eg\x89\n\xbc\xde\xf0")

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
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)),
            100000000000000000000000,
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6),
            unhexlify("60006000600039600051600055"),
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
        self.assertEqual(solve(world.current_vm.gas), 99999994976)

    def test_caller(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: caller.json
        sha256sum: 4529f1e1bec3e237c6c94f8ae1c7c2aabd8c2e5b0d0292ff493b7a5707def563
        Code:     CALLER
                  PUSH1 0x0
                  SSTORE
        """

        def solve(val):
            return self._solve(constraints, val)

        constraints = ConstraintSet()

        blocknumber = constraints.new_bitvec(256, name="blocknumber")
        constraints.add(blocknumber == 0)

        timestamp = constraints.new_bitvec(256, name="timestamp")
        constraints.add(timestamp == 1)

        difficulty = constraints.new_bitvec(256, name="difficulty")
        constraints.add(difficulty == 256)

        coinbase = constraints.new_bitvec(256, name="coinbase")
        constraints.add(coinbase == 244687034288125203496486448490407391986876152250)

        gaslimit = constraints.new_bitvec(256, name="gaslimit")
        constraints.add(gaslimit == 1000000)

        world = evm.EVMWorld(
            constraints,
            blocknumber=blocknumber,
            timestamp=timestamp,
            difficulty=difficulty,
            coinbase=coinbase,
            gaslimit=gaslimit,
        )

        acc_addr = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        acc_code = unhexlify("33600055")

        acc_balance = constraints.new_bitvec(
            256, name="balance_0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6"
        )
        constraints.add(acc_balance == 100000000000000000000000)

        acc_nonce = constraints.new_bitvec(
            256, name="nonce_0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6"
        )
        constraints.add(acc_nonce == 0)

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F3947DEF4CF144679DA39C4C32BDC35681
        price = constraints.new_bitvec(256, name="price")
        constraints.add(price == 1000000000)

        value = constraints.new_bitvec(256, name="value")
        constraints.add(value == 1000000000000000000)

        gas = constraints.new_bitvec(256, name="gas")
        constraints.add(gas == 100000000000)

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
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)),
            100000000000000000000000,
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6), unhexlify("33600055")
        )
        # check storage
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x00)),
            0xCD1722F3947DEF4CF144679DA39C4C32BDC35681,
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
        self.assertEqual(solve(world.current_vm.gas), 99999979995)

    def test_calldatacopy0_return(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: calldatacopy0_return.json
        sha256sum: 9e74e8f70e7afaed68c71a3e0ed112039672e9b6230b04e9150c22a43d59d654
        Code:     PUSH1 0x2
                  PUSH1 0x1
                  PUSH1 0x0
                  CALLDATACOPY
                  PUSH1 0x0
                  MLOAD
                  PUSH1 0x0
                  SSTORE
                  MSIZE
                  PUSH1 0x0
                  RETURN
        """

        def solve(val):
            return self._solve(constraints, val)

        constraints = ConstraintSet()

        blocknumber = constraints.new_bitvec(256, name="blocknumber")
        constraints.add(blocknumber == 0)

        timestamp = constraints.new_bitvec(256, name="timestamp")
        constraints.add(timestamp == 1)

        difficulty = constraints.new_bitvec(256, name="difficulty")
        constraints.add(difficulty == 256)

        coinbase = constraints.new_bitvec(256, name="coinbase")
        constraints.add(coinbase == 244687034288125203496486448490407391986876152250)

        gaslimit = constraints.new_bitvec(256, name="gaslimit")
        constraints.add(gaslimit == 1000000)

        world = evm.EVMWorld(
            constraints,
            blocknumber=blocknumber,
            timestamp=timestamp,
            difficulty=difficulty,
            coinbase=coinbase,
            gaslimit=gaslimit,
        )

        acc_addr = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        acc_code = unhexlify("60026001600037600051600055596000f3")

        acc_balance = constraints.new_bitvec(
            256, name="balance_0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6"
        )
        constraints.add(acc_balance == 1000000000000000000)

        acc_nonce = constraints.new_bitvec(
            256, name="nonce_0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6"
        )
        constraints.add(acc_nonce == 0)

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F3947DEF4CF144679DA39C4C32BDC35681
        price = constraints.new_bitvec(256, name="price")
        constraints.add(price == 1000000000)

        value = constraints.new_bitvec(256, name="value")
        constraints.add(value == 1000000000000000000)

        gas = constraints.new_bitvec(256, name="gas")
        constraints.add(gas == 100000000000)

        data = constraints.new_array(index_max=17)
        constraints.add(data == b"\x124Vx\x90\xab\xcd\xef\x01#Eg\x89\n\xbc\xde\xf0")

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
            unhexlify("60026001600037600051600055596000f3"),
        )
        # check storage
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x00)),
            0x3456000000000000000000000000000000000000000000000000000000000000,
        )
        # check outs
        self.assertEqual(
            returndata,
            unhexlify("3456000000000000000000000000000000000000000000000000000000000000"),
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
        self.assertEqual(solve(world.current_vm.gas), 99999979968)

    def test_calldatacopy0(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: calldatacopy0.json
        sha256sum: 638df00ff9e8cdcfa8b3d3cc5271a67361774e8c92ed2effd1efed8d79de1354
        Code:     PUSH1 0x2
                  PUSH1 0x1
                  PUSH1 0x0
                  CALLDATACOPY
                  PUSH1 0x0
                  MLOAD
                  PUSH1 0x0
                  SSTORE
        """

        def solve(val):
            return self._solve(constraints, val)

        constraints = ConstraintSet()

        blocknumber = constraints.new_bitvec(256, name="blocknumber")
        constraints.add(blocknumber == 0)

        timestamp = constraints.new_bitvec(256, name="timestamp")
        constraints.add(timestamp == 1)

        difficulty = constraints.new_bitvec(256, name="difficulty")
        constraints.add(difficulty == 256)

        coinbase = constraints.new_bitvec(256, name="coinbase")
        constraints.add(coinbase == 244687034288125203496486448490407391986876152250)

        gaslimit = constraints.new_bitvec(256, name="gaslimit")
        constraints.add(gaslimit == 1000000)

        world = evm.EVMWorld(
            constraints,
            blocknumber=blocknumber,
            timestamp=timestamp,
            difficulty=difficulty,
            coinbase=coinbase,
            gaslimit=gaslimit,
        )

        acc_addr = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        acc_code = unhexlify("60026001600037600051600055")

        acc_balance = constraints.new_bitvec(
            256, name="balance_0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6"
        )
        constraints.add(acc_balance == 100000000000000000000000)

        acc_nonce = constraints.new_bitvec(
            256, name="nonce_0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6"
        )
        constraints.add(acc_nonce == 0)

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F3947DEF4CF144679DA39C4C32BDC35681
        price = constraints.new_bitvec(256, name="price")
        constraints.add(price == 1000000000)

        value = constraints.new_bitvec(256, name="value")
        constraints.add(value == 1000000000000000000)

        gas = constraints.new_bitvec(256, name="gas")
        constraints.add(gas == 100000000000)

        data = constraints.new_array(index_max=17)
        constraints.add(data == b"\x124Vx\x90\xab\xcd\xef\x01#Eg\x89\n\xbc\xde\xf0")

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
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)),
            100000000000000000000000,
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6),
            unhexlify("60026001600037600051600055"),
        )
        # check storage
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x00)),
            0x3456000000000000000000000000000000000000000000000000000000000000,
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
        self.assertEqual(solve(world.current_vm.gas), 99999979973)

    def test_calldataloadSizeTooHigh(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: calldataloadSizeTooHigh.json
        sha256sum: 221a833196ffed6d0105c63c512f94be030460c5318e131ba85eab390e248521
        Code:     PUSH32 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffa
                  CALLDATALOAD
                  PUSH1 0x0
                  SSTORE
        """

        def solve(val):
            return self._solve(constraints, val)

        constraints = ConstraintSet()

        blocknumber = constraints.new_bitvec(256, name="blocknumber")
        constraints.add(blocknumber == 0)

        timestamp = constraints.new_bitvec(256, name="timestamp")
        constraints.add(timestamp == 1)

        difficulty = constraints.new_bitvec(256, name="difficulty")
        constraints.add(difficulty == 256)

        coinbase = constraints.new_bitvec(256, name="coinbase")
        constraints.add(coinbase == 244687034288125203496486448490407391986876152250)

        gaslimit = constraints.new_bitvec(256, name="gaslimit")
        constraints.add(gaslimit == 1000000)

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
            "7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffa35600055"
        )

        acc_balance = constraints.new_bitvec(
            256, name="balance_0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6"
        )
        constraints.add(acc_balance == 100000000000000000000000)

        acc_nonce = constraints.new_bitvec(
            256, name="nonce_0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6"
        )
        constraints.add(acc_nonce == 0)

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F3947DEF4CF144679DA39C4C32BDC35681
        price = constraints.new_bitvec(256, name="price")
        constraints.add(price == 1000000000)

        value = constraints.new_bitvec(256, name="value")
        constraints.add(value == 1000000000000000000)

        gas = constraints.new_bitvec(256, name="gas")
        constraints.add(gas == 100000000000)

        data = constraints.new_array(index_max=34)
        constraints.add(
            data
            == b"\x124Vx\x9a\xbc\xde\xf0\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00$"
        )

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
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)),
            100000000000000000000000,
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6),
            unhexlify("7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffa35600055"),
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
        self.assertEqual(solve(world.current_vm.gas), 99999994991)

    def test_calldatasize1(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: calldatasize1.json
        sha256sum: f544d9df8a4efd692589f75cc18a39449e86929ab2774d4838587f826f0ccc1c
        Code:     CALLDATASIZE
                  PUSH1 0x0
                  SSTORE
        """

        def solve(val):
            return self._solve(constraints, val)

        constraints = ConstraintSet()

        blocknumber = constraints.new_bitvec(256, name="blocknumber")
        constraints.add(blocknumber == 0)

        timestamp = constraints.new_bitvec(256, name="timestamp")
        constraints.add(timestamp == 1)

        difficulty = constraints.new_bitvec(256, name="difficulty")
        constraints.add(difficulty == 256)

        coinbase = constraints.new_bitvec(256, name="coinbase")
        constraints.add(coinbase == 244687034288125203496486448490407391986876152250)

        gaslimit = constraints.new_bitvec(256, name="gaslimit")
        constraints.add(gaslimit == 1000000)

        world = evm.EVMWorld(
            constraints,
            blocknumber=blocknumber,
            timestamp=timestamp,
            difficulty=difficulty,
            coinbase=coinbase,
            gaslimit=gaslimit,
        )

        acc_addr = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        acc_code = unhexlify("36600055")

        acc_balance = constraints.new_bitvec(
            256, name="balance_0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6"
        )
        constraints.add(acc_balance == 100000000000000000000000)

        acc_nonce = constraints.new_bitvec(
            256, name="nonce_0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6"
        )
        constraints.add(acc_nonce == 0)

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F3947DEF4CF144679DA39C4C32BDC35681
        price = constraints.new_bitvec(256, name="price")
        constraints.add(price == 1000000000)

        value = constraints.new_bitvec(256, name="value")
        constraints.add(value == 1000000000000000000)

        gas = constraints.new_bitvec(256, name="gas")
        constraints.add(gas == 100000000000)

        data = constraints.new_array(index_max=33)
        constraints.add(
            data
            == b"\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff#"
        )

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
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)),
            100000000000000000000000,
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6), unhexlify("36600055")
        )
        # check storage
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x00)), 0x21
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
        self.assertEqual(solve(world.current_vm.gas), 99999979995)

    def test_calldatacopyUnderFlow(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: calldatacopyUnderFlow.json
        sha256sum: 3343d3f1ad16987085ce1b5c96dc1464ee1e6fdbdc487dd300e73977c3e5eb45
        Code:     PUSH1 0x1
                  PUSH1 0x2
                  CALLDATACOPY
        """

        def solve(val):
            return self._solve(constraints, val)

        constraints = ConstraintSet()

        blocknumber = constraints.new_bitvec(256, name="blocknumber")
        constraints.add(blocknumber == 0)

        timestamp = constraints.new_bitvec(256, name="timestamp")
        constraints.add(timestamp == 1)

        difficulty = constraints.new_bitvec(256, name="difficulty")
        constraints.add(difficulty == 256)

        coinbase = constraints.new_bitvec(256, name="coinbase")
        constraints.add(coinbase == 244687034288125203496486448490407391986876152250)

        gaslimit = constraints.new_bitvec(256, name="gaslimit")
        constraints.add(gaslimit == 1000000)

        world = evm.EVMWorld(
            constraints,
            blocknumber=blocknumber,
            timestamp=timestamp,
            difficulty=difficulty,
            coinbase=coinbase,
            gaslimit=gaslimit,
        )

        acc_addr = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        acc_code = unhexlify("6001600237")

        acc_balance = constraints.new_bitvec(
            256, name="balance_0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6"
        )
        constraints.add(acc_balance == 100000000000000000000000)

        acc_nonce = constraints.new_bitvec(
            256, name="nonce_0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6"
        )
        constraints.add(acc_nonce == 0)

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F3947DEF4CF144679DA39C4C32BDC35681
        price = constraints.new_bitvec(256, name="price")
        constraints.add(price == 1000000000)

        value = constraints.new_bitvec(256, name="value")
        constraints.add(value == 1000000000000000000)

        gas = constraints.new_bitvec(256, name="gas")
        constraints.add(gas == 100000000000)

        data = constraints.new_array(index_max=17)
        constraints.add(data == b"\x124Vx\x90\xab\xcd\xef\x01#Eg\x89\n\xbc\xde\xf0")

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

    def test_address0(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: address0.json
        sha256sum: 2eadf1924441917e8a8e10f2749612b68a41846ccb185dd528ea65f3257d45db
        Code:     ADDRESS
                  PUSH1 0x0
                  SSTORE
        """

        def solve(val):
            return self._solve(constraints, val)

        constraints = ConstraintSet()

        blocknumber = constraints.new_bitvec(256, name="blocknumber")
        constraints.add(blocknumber == 0)

        timestamp = constraints.new_bitvec(256, name="timestamp")
        constraints.add(timestamp == 1)

        difficulty = constraints.new_bitvec(256, name="difficulty")
        constraints.add(difficulty == 256)

        coinbase = constraints.new_bitvec(256, name="coinbase")
        constraints.add(coinbase == 244687034288125203496486448490407391986876152250)

        gaslimit = constraints.new_bitvec(256, name="gaslimit")
        constraints.add(gaslimit == 1000000)

        world = evm.EVMWorld(
            constraints,
            blocknumber=blocknumber,
            timestamp=timestamp,
            difficulty=difficulty,
            coinbase=coinbase,
            gaslimit=gaslimit,
        )

        acc_addr = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        acc_code = unhexlify("30600055")

        acc_balance = constraints.new_bitvec(
            256, name="balance_0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6"
        )
        constraints.add(acc_balance == 100000000000000000000000)

        acc_nonce = constraints.new_bitvec(
            256, name="nonce_0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6"
        )
        constraints.add(acc_nonce == 0)

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F3947DEF4CF144679DA39C4C32BDC35681
        price = constraints.new_bitvec(256, name="price")
        constraints.add(price == 1000000000)

        value = constraints.new_bitvec(256, name="value")
        constraints.add(value == 1000000000000000000)

        gas = constraints.new_bitvec(256, name="gas")
        constraints.add(gas == 100000000000)

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
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)),
            100000000000000000000000,
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6), unhexlify("30600055")
        )
        # check storage
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x00)),
            0x0F572E5295C57F15886F9B263E2F6D2D6C7B5EC6,
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
        self.assertEqual(solve(world.current_vm.gas), 99999979995)

    def test_codecopy0(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: codecopy0.json
        sha256sum: ec91f06ad11895315200c4a39a61ef367b82003e0b7cdb8bbfad4c143694c32f
        Code:     PUSH1 0x5
                  PUSH1 0x0
                  PUSH1 0x0
                  CODECOPY
                  PUSH1 0x0
                  MLOAD
                  PUSH1 0x0
                  SSTORE
        """

        def solve(val):
            return self._solve(constraints, val)

        constraints = ConstraintSet()

        blocknumber = constraints.new_bitvec(256, name="blocknumber")
        constraints.add(blocknumber == 0)

        timestamp = constraints.new_bitvec(256, name="timestamp")
        constraints.add(timestamp == 1)

        difficulty = constraints.new_bitvec(256, name="difficulty")
        constraints.add(difficulty == 256)

        coinbase = constraints.new_bitvec(256, name="coinbase")
        constraints.add(coinbase == 244687034288125203496486448490407391986876152250)

        gaslimit = constraints.new_bitvec(256, name="gaslimit")
        constraints.add(gaslimit == 1000000)

        world = evm.EVMWorld(
            constraints,
            blocknumber=blocknumber,
            timestamp=timestamp,
            difficulty=difficulty,
            coinbase=coinbase,
            gaslimit=gaslimit,
        )

        acc_addr = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        acc_code = unhexlify("60056000600039600051600055")

        acc_balance = constraints.new_bitvec(
            256, name="balance_0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6"
        )
        constraints.add(acc_balance == 100000000000000000000000)

        acc_nonce = constraints.new_bitvec(
            256, name="nonce_0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6"
        )
        constraints.add(acc_nonce == 0)

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F3947DEF4CF144679DA39C4C32BDC35681
        price = constraints.new_bitvec(256, name="price")
        constraints.add(price == 1000000000)

        value = constraints.new_bitvec(256, name="value")
        constraints.add(value == 1000000000000000000)

        gas = constraints.new_bitvec(256, name="gas")
        constraints.add(gas == 100000000000)

        data = constraints.new_array(index_max=17)
        constraints.add(data == b"\x124Vx\x90\xab\xcd\xef\x01#Eg\x89\n\xbc\xde\xf0")

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
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)),
            100000000000000000000000,
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6),
            unhexlify("60056000600039600051600055"),
        )
        # check storage
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x00)),
            0x6005600060000000000000000000000000000000000000000000000000000000,
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
        self.assertEqual(solve(world.current_vm.gas), 99999979973)

    def test_codecopy_DataIndexTooHigh(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: codecopy_DataIndexTooHigh.json
        sha256sum: b3eb9e9d3f51705e51de5db4bfabe4d3932c4046b242f6730f875b5221eea132
        Code:     PUSH1 0x8
                  PUSH32 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffa
                  PUSH1 0x0
                  CODECOPY
                  PUSH1 0x0
                  MLOAD
                  PUSH1 0x0
                  SSTORE
        """

        def solve(val):
            return self._solve(constraints, val)

        constraints = ConstraintSet()

        blocknumber = constraints.new_bitvec(256, name="blocknumber")
        constraints.add(blocknumber == 0)

        timestamp = constraints.new_bitvec(256, name="timestamp")
        constraints.add(timestamp == 1)

        difficulty = constraints.new_bitvec(256, name="difficulty")
        constraints.add(difficulty == 256)

        coinbase = constraints.new_bitvec(256, name="coinbase")
        constraints.add(coinbase == 244687034288125203496486448490407391986876152250)

        gaslimit = constraints.new_bitvec(256, name="gaslimit")
        constraints.add(gaslimit == 1000000)

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
            "60087ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffa600039600051600055"
        )

        acc_balance = constraints.new_bitvec(
            256, name="balance_0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6"
        )
        constraints.add(acc_balance == 100000000000000000000000)

        acc_nonce = constraints.new_bitvec(
            256, name="nonce_0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6"
        )
        constraints.add(acc_nonce == 0)

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F3947DEF4CF144679DA39C4C32BDC35681
        price = constraints.new_bitvec(256, name="price")
        constraints.add(price == 1000000000)

        value = constraints.new_bitvec(256, name="value")
        constraints.add(value == 1000000000000000000)

        gas = constraints.new_bitvec(256, name="gas")
        constraints.add(gas == 100000000000)

        data = constraints.new_array(index_max=17)
        constraints.add(data == b"\x124Vx\x90\xab\xcd\xef\x01#Eg\x89\n\xbc\xde\xf0")

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
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)),
            100000000000000000000000,
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6),
            unhexlify(
                "60087ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffa600039600051600055"
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
        self.assertEqual(solve(world.current_vm.gas), 99999994973)

    def test_calldatacopy2(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: calldatacopy2.json
        sha256sum: 5ef7b5e2acb1896f30f62017bd2e18a56c921199605389378c7abec55031cc20
        Code:     PUSH1 0x0
                  PUSH1 0x1
                  PUSH1 0x0
                  CALLDATACOPY
                  PUSH1 0x0
                  MLOAD
                  PUSH1 0x0
                  SSTORE
        """

        def solve(val):
            return self._solve(constraints, val)

        constraints = ConstraintSet()

        blocknumber = constraints.new_bitvec(256, name="blocknumber")
        constraints.add(blocknumber == 0)

        timestamp = constraints.new_bitvec(256, name="timestamp")
        constraints.add(timestamp == 1)

        difficulty = constraints.new_bitvec(256, name="difficulty")
        constraints.add(difficulty == 256)

        coinbase = constraints.new_bitvec(256, name="coinbase")
        constraints.add(coinbase == 244687034288125203496486448490407391986876152250)

        gaslimit = constraints.new_bitvec(256, name="gaslimit")
        constraints.add(gaslimit == 1000000)

        world = evm.EVMWorld(
            constraints,
            blocknumber=blocknumber,
            timestamp=timestamp,
            difficulty=difficulty,
            coinbase=coinbase,
            gaslimit=gaslimit,
        )

        acc_addr = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        acc_code = unhexlify("60006001600037600051600055")

        acc_balance = constraints.new_bitvec(
            256, name="balance_0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6"
        )
        constraints.add(acc_balance == 100000000000000000000000)

        acc_nonce = constraints.new_bitvec(
            256, name="nonce_0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6"
        )
        constraints.add(acc_nonce == 0)

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F3947DEF4CF144679DA39C4C32BDC35681
        price = constraints.new_bitvec(256, name="price")
        constraints.add(price == 1000000000)

        value = constraints.new_bitvec(256, name="value")
        constraints.add(value == 1000000000000000000)

        gas = constraints.new_bitvec(256, name="gas")
        constraints.add(gas == 100000000000)

        data = constraints.new_array(index_max=17)
        constraints.add(data == b"\x124Vx\x90\xab\xcd\xef\x01#Eg\x89\n\xbc\xde\xf0")

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
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)),
            100000000000000000000000,
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6),
            unhexlify("60006001600037600051600055"),
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
        self.assertEqual(solve(world.current_vm.gas), 99999994976)

    def test_calldatacopyZeroMemExpansion_return(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: calldatacopyZeroMemExpansion_return.json
        sha256sum: 403ef747fa5eaea2cd79876ed9060188c5f3016501a0028f1de700e6a33bf5ac
        Code:     PUSH1 0x0
                  PUSH1 0x0
                  PUSH1 0x0
                  CALLDATACOPY
                  PUSH1 0x0
                  MLOAD
                  PUSH1 0x0
                  SSTORE
                  MSIZE
                  PUSH1 0x0
                  RETURN
        """

        def solve(val):
            return self._solve(constraints, val)

        constraints = ConstraintSet()

        blocknumber = constraints.new_bitvec(256, name="blocknumber")
        constraints.add(blocknumber == 0)

        timestamp = constraints.new_bitvec(256, name="timestamp")
        constraints.add(timestamp == 1)

        difficulty = constraints.new_bitvec(256, name="difficulty")
        constraints.add(difficulty == 256)

        coinbase = constraints.new_bitvec(256, name="coinbase")
        constraints.add(coinbase == 244687034288125203496486448490407391986876152250)

        gaslimit = constraints.new_bitvec(256, name="gaslimit")
        constraints.add(gaslimit == 1000000)

        world = evm.EVMWorld(
            constraints,
            blocknumber=blocknumber,
            timestamp=timestamp,
            difficulty=difficulty,
            coinbase=coinbase,
            gaslimit=gaslimit,
        )

        acc_addr = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        acc_code = unhexlify("60006000600037600051600055596000f3")

        acc_balance = constraints.new_bitvec(
            256, name="balance_0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6"
        )
        constraints.add(acc_balance == 1000000000000000000)

        acc_nonce = constraints.new_bitvec(
            256, name="nonce_0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6"
        )
        constraints.add(acc_nonce == 0)

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F3947DEF4CF144679DA39C4C32BDC35681
        price = constraints.new_bitvec(256, name="price")
        constraints.add(price == 1000000000)

        value = constraints.new_bitvec(256, name="value")
        constraints.add(value == 1000000000000000000)

        gas = constraints.new_bitvec(256, name="gas")
        constraints.add(gas == 100000000000)

        data = constraints.new_array(index_max=17)
        constraints.add(data == b"\x124Vx\x90\xab\xcd\xef\x01#Eg\x89\n\xbc\xde\xf0")

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
            unhexlify("60006000600037600051600055596000f3"),
        )
        # check outs
        self.assertEqual(
            returndata,
            unhexlify("0000000000000000000000000000000000000000000000000000000000000000"),
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
        self.assertEqual(solve(world.current_vm.gas), 99999994971)

    def test_calldatacopy_sec(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: calldatacopy_sec.json
        sha256sum: f6348aac4068d1096c0c4ae56b253f94d93516c0c9d6274018d5573d5e6ec6d5
        Code:     PUSH1 0x5
                  JUMP
                  JUMPDEST
                  STOP
                  JUMPDEST
                  PUSH1 0x42
                  PUSH1 0x1f
                  MSTORE8
                  PUSH2 0x103
                  PUSH1 0x0
                  PUSH1 0x1f
                  CALLDATACOPY
                  PUSH1 0x0
                  MLOAD
                  DUP1
                  PUSH1 0x60
                  EQ
                  PUSH1 0x3
                  JUMPI
                  PUSH5 0xbadc0ffee
                  PUSH1 0xff
                  SSTORE
        """

        def solve(val):
            return self._solve(constraints, val)

        constraints = ConstraintSet()

        blocknumber = constraints.new_bitvec(256, name="blocknumber")
        constraints.add(blocknumber == 0)

        timestamp = constraints.new_bitvec(256, name="timestamp")
        constraints.add(timestamp == 1)

        difficulty = constraints.new_bitvec(256, name="difficulty")
        constraints.add(difficulty == 256)

        coinbase = constraints.new_bitvec(256, name="coinbase")
        constraints.add(coinbase == 244687034288125203496486448490407391986876152250)

        gaslimit = constraints.new_bitvec(256, name="gaslimit")
        constraints.add(gaslimit == 1000000)

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
            "6005565b005b6042601f536101036000601f3760005180606014600357640badc0ffee60ff55"
        )

        acc_balance = constraints.new_bitvec(
            256, name="balance_0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6"
        )
        constraints.add(acc_balance == 1000000000000000000)

        acc_nonce = constraints.new_bitvec(
            256, name="nonce_0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6"
        )
        constraints.add(acc_nonce == 0)

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F3947DEF4CF144679DA39C4C32BDC35681
        price = constraints.new_bitvec(256, name="price")
        constraints.add(price == 1000000000)

        value = constraints.new_bitvec(256, name="value")
        constraints.add(value == 1000000000000000000)

        gas = constraints.new_bitvec(256, name="gas")
        constraints.add(gas == 100000000000)

        data = constraints.new_array(index_max=17)
        constraints.add(data == b"\x124Vx\x90\xab\xcd\xef\x01#Eg\x89\n\xbc\xde\xf0")

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
                "6005565b005b6042601f536101036000601f3760005180606014600357640badc0ffee60ff55"
            ),
        )
        # check storage
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0xFF)),
            0x0BADC0FFEE,
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
        self.assertEqual(solve(world.current_vm.gas), 99999979876)

    def test_gasprice(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: gasprice.json
        sha256sum: 8764def18ca712c2d9c7fc2f139d2adc67016f3825f05959e23151ca2461c885
        Code:     GASPRICE
                  PUSH1 0x0
                  SSTORE
        """

        def solve(val):
            return self._solve(constraints, val)

        constraints = ConstraintSet()

        blocknumber = constraints.new_bitvec(256, name="blocknumber")
        constraints.add(blocknumber == 0)

        timestamp = constraints.new_bitvec(256, name="timestamp")
        constraints.add(timestamp == 1)

        difficulty = constraints.new_bitvec(256, name="difficulty")
        constraints.add(difficulty == 256)

        coinbase = constraints.new_bitvec(256, name="coinbase")
        constraints.add(coinbase == 244687034288125203496486448490407391986876152250)

        gaslimit = constraints.new_bitvec(256, name="gaslimit")
        constraints.add(gaslimit == 1000000)

        world = evm.EVMWorld(
            constraints,
            blocknumber=blocknumber,
            timestamp=timestamp,
            difficulty=difficulty,
            coinbase=coinbase,
            gaslimit=gaslimit,
        )

        acc_addr = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        acc_code = unhexlify("3a600055")

        acc_balance = constraints.new_bitvec(
            256, name="balance_0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6"
        )
        constraints.add(acc_balance == 100000000000000000000000)

        acc_nonce = constraints.new_bitvec(
            256, name="nonce_0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6"
        )
        constraints.add(acc_nonce == 0)

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F3947DEF4CF144679DA39C4C32BDC35681
        price = constraints.new_bitvec(256, name="price")
        constraints.add(price == 123456789)

        value = constraints.new_bitvec(256, name="value")
        constraints.add(value == 1000000000000000000)

        gas = constraints.new_bitvec(256, name="gas")
        constraints.add(gas == 100000000000)

        data = constraints.new_array(index_max=17)
        constraints.add(data == b"\x124Vx\x90\xab\xcd\xef\x01#Eg\x89\n\xbc\xde\xf0")

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
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)),
            100000000000000000000000,
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6), unhexlify("3a600055")
        )
        # check storage
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x00)),
            0x075BCD15,
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
        self.assertEqual(solve(world.current_vm.gas), 99999979995)

    def test_calldataload1(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: calldataload1.json
        sha256sum: 890c4de64840f5e42274ebd0a6058a75ee9d7fd347dbd4e28fe91db2a935b813
        Code:     PUSH1 0x1
                  CALLDATALOAD
                  PUSH1 0x0
                  SSTORE
        """

        def solve(val):
            return self._solve(constraints, val)

        constraints = ConstraintSet()

        blocknumber = constraints.new_bitvec(256, name="blocknumber")
        constraints.add(blocknumber == 0)

        timestamp = constraints.new_bitvec(256, name="timestamp")
        constraints.add(timestamp == 1)

        difficulty = constraints.new_bitvec(256, name="difficulty")
        constraints.add(difficulty == 256)

        coinbase = constraints.new_bitvec(256, name="coinbase")
        constraints.add(coinbase == 244687034288125203496486448490407391986876152250)

        gaslimit = constraints.new_bitvec(256, name="gaslimit")
        constraints.add(gaslimit == 1000000)

        world = evm.EVMWorld(
            constraints,
            blocknumber=blocknumber,
            timestamp=timestamp,
            difficulty=difficulty,
            coinbase=coinbase,
            gaslimit=gaslimit,
        )

        acc_addr = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        acc_code = unhexlify("600135600055")

        acc_balance = constraints.new_bitvec(
            256, name="balance_0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6"
        )
        constraints.add(acc_balance == 100000000000000000000000)

        acc_nonce = constraints.new_bitvec(
            256, name="nonce_0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6"
        )
        constraints.add(acc_nonce == 0)

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F3947DEF4CF144679DA39C4C32BDC35681
        price = constraints.new_bitvec(256, name="price")
        constraints.add(price == 1000000000)

        value = constraints.new_bitvec(256, name="value")
        constraints.add(value == 1000000000000000000)

        gas = constraints.new_bitvec(256, name="gas")
        constraints.add(gas == 100000000000)

        data = constraints.new_array(index_max=33)
        constraints.add(
            data
            == b"\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff#"
        )

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
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)),
            100000000000000000000000,
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6), unhexlify("600135600055")
        )
        # check storage
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x00)),
            0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF23,
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
        self.assertEqual(solve(world.current_vm.gas), 99999979991)

    def test_calldatacopy_DataIndexTooHigh(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: calldatacopy_DataIndexTooHigh.json
        sha256sum: f6113b84185521a92e9507abdcacb7ff31088a74130ca1c1dbd5c37ed20b3e1a
        Code:     PUSH1 0xff
                  PUSH32 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffa
                  PUSH1 0x0
                  CALLDATACOPY
                  PUSH1 0x0
                  MLOAD
                  PUSH1 0x0
                  SSTORE
        """

        def solve(val):
            return self._solve(constraints, val)

        constraints = ConstraintSet()

        blocknumber = constraints.new_bitvec(256, name="blocknumber")
        constraints.add(blocknumber == 0)

        timestamp = constraints.new_bitvec(256, name="timestamp")
        constraints.add(timestamp == 1)

        difficulty = constraints.new_bitvec(256, name="difficulty")
        constraints.add(difficulty == 256)

        coinbase = constraints.new_bitvec(256, name="coinbase")
        constraints.add(coinbase == 244687034288125203496486448490407391986876152250)

        gaslimit = constraints.new_bitvec(256, name="gaslimit")
        constraints.add(gaslimit == 1000000)

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
            "60ff7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffa600037600051600055"
        )

        acc_balance = constraints.new_bitvec(
            256, name="balance_0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6"
        )
        constraints.add(acc_balance == 100000000000000000000000)

        acc_nonce = constraints.new_bitvec(
            256, name="nonce_0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6"
        )
        constraints.add(acc_nonce == 0)

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F3947DEF4CF144679DA39C4C32BDC35681
        price = constraints.new_bitvec(256, name="price")
        constraints.add(price == 1000000000)

        value = constraints.new_bitvec(256, name="value")
        constraints.add(value == 1000000000000000000)

        gas = constraints.new_bitvec(256, name="gas")
        constraints.add(gas == 100000000000)

        data = constraints.new_array(index_max=17)
        constraints.add(data == b"\x124Vx\x90\xab\xcd\xef\x01#Eg\x89\n\xbc\xde\xf0")

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
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)),
            100000000000000000000000,
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6),
            unhexlify(
                "60ff7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffa600037600051600055"
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
        self.assertEqual(solve(world.current_vm.gas), 99999994931)

    def test_calldataload_BigOffset(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: calldataload_BigOffset.json
        sha256sum: eb1de5f0bd53b3b3a0aeafb9078c11812ab0995cf6b3212bee54bb00cd94b4cb
        Code:     PUSH32 0x4200000000000000000000000000000000000000000000000000000000000000
                  CALLDATALOAD
                  PUSH1 0x0
                  SSTORE
        """

        def solve(val):
            return self._solve(constraints, val)

        constraints = ConstraintSet()

        blocknumber = constraints.new_bitvec(256, name="blocknumber")
        constraints.add(blocknumber == 0)

        timestamp = constraints.new_bitvec(256, name="timestamp")
        constraints.add(timestamp == 1)

        difficulty = constraints.new_bitvec(256, name="difficulty")
        constraints.add(difficulty == 256)

        coinbase = constraints.new_bitvec(256, name="coinbase")
        constraints.add(coinbase == 244687034288125203496486448490407391986876152250)

        gaslimit = constraints.new_bitvec(256, name="gaslimit")
        constraints.add(gaslimit == 1000000)

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
            "7f420000000000000000000000000000000000000000000000000000000000000035600055"
        )

        acc_balance = constraints.new_bitvec(
            256, name="balance_0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6"
        )
        constraints.add(acc_balance == 100000000000000000000000)

        acc_nonce = constraints.new_bitvec(
            256, name="nonce_0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6"
        )
        constraints.add(acc_nonce == 0)

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F3947DEF4CF144679DA39C4C32BDC35681
        price = constraints.new_bitvec(256, name="price")
        constraints.add(price == 1000000000)

        value = constraints.new_bitvec(256, name="value")
        constraints.add(value == 1000000000000000000)

        gas = constraints.new_bitvec(256, name="gas")
        constraints.add(gas == 100000000000)

        data = constraints.new_array(index_max=32)
        constraints.add(
            data
            == b"B\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00"
        )

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
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)),
            100000000000000000000000,
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6),
            unhexlify("7f420000000000000000000000000000000000000000000000000000000000000035600055"),
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
        self.assertEqual(solve(world.current_vm.gas), 99999994991)

    def test_calldatacopy_DataIndexTooHigh2_return(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: calldatacopy_DataIndexTooHigh2_return.json
        sha256sum: 5ba7945dab6966e02c974e2be43558840c4331a57508e0ae96fd29bdec697f85
        Code:     PUSH1 0x9
                  PUSH32 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffa
                  PUSH1 0x0
                  CALLDATACOPY
                  PUSH1 0x0
                  MLOAD
                  PUSH1 0x0
                  SSTORE
                  MSIZE
                  PUSH1 0x0
                  RETURN
        """

        def solve(val):
            return self._solve(constraints, val)

        constraints = ConstraintSet()

        blocknumber = constraints.new_bitvec(256, name="blocknumber")
        constraints.add(blocknumber == 0)

        timestamp = constraints.new_bitvec(256, name="timestamp")
        constraints.add(timestamp == 1)

        difficulty = constraints.new_bitvec(256, name="difficulty")
        constraints.add(difficulty == 256)

        coinbase = constraints.new_bitvec(256, name="coinbase")
        constraints.add(coinbase == 244687034288125203496486448490407391986876152250)

        gaslimit = constraints.new_bitvec(256, name="gaslimit")
        constraints.add(gaslimit == 1000000)

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
            "60097ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffa600037600051600055596000f3"
        )

        acc_balance = constraints.new_bitvec(
            256, name="balance_0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6"
        )
        constraints.add(acc_balance == 1000000000000000000)

        acc_nonce = constraints.new_bitvec(
            256, name="nonce_0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6"
        )
        constraints.add(acc_nonce == 0)

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F3947DEF4CF144679DA39C4C32BDC35681
        price = constraints.new_bitvec(256, name="price")
        constraints.add(price == 1000000000)

        value = constraints.new_bitvec(256, name="value")
        constraints.add(value == 1000000000000000000)

        gas = constraints.new_bitvec(256, name="gas")
        constraints.add(gas == 100000000000)

        data = constraints.new_array(index_max=17)
        constraints.add(data == b"\x124Vx\x90\xab\xcd\xef\x01#Eg\x89\n\xbc\xde\xf0")

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
                "60097ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffa600037600051600055596000f3"
            ),
        )
        # check outs
        self.assertEqual(
            returndata,
            unhexlify("0000000000000000000000000000000000000000000000000000000000000000"),
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
        self.assertEqual(solve(world.current_vm.gas), 99999994968)

    def test_calldataload2(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: calldataload2.json
        sha256sum: 3e2a38159468be9c41b09413dfbf0047ff168e367d6e6ef183be6a8b43cf3da6
        Code:     PUSH1 0x5
                  CALLDATALOAD
                  PUSH1 0x0
                  SSTORE
        """

        def solve(val):
            return self._solve(constraints, val)

        constraints = ConstraintSet()

        blocknumber = constraints.new_bitvec(256, name="blocknumber")
        constraints.add(blocknumber == 0)

        timestamp = constraints.new_bitvec(256, name="timestamp")
        constraints.add(timestamp == 1)

        difficulty = constraints.new_bitvec(256, name="difficulty")
        constraints.add(difficulty == 256)

        coinbase = constraints.new_bitvec(256, name="coinbase")
        constraints.add(coinbase == 244687034288125203496486448490407391986876152250)

        gaslimit = constraints.new_bitvec(256, name="gaslimit")
        constraints.add(gaslimit == 1000000)

        world = evm.EVMWorld(
            constraints,
            blocknumber=blocknumber,
            timestamp=timestamp,
            difficulty=difficulty,
            coinbase=coinbase,
            gaslimit=gaslimit,
        )

        acc_addr = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        acc_code = unhexlify("600535600055")

        acc_balance = constraints.new_bitvec(
            256, name="balance_0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6"
        )
        constraints.add(acc_balance == 100000000000000000000000)

        acc_nonce = constraints.new_bitvec(
            256, name="nonce_0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6"
        )
        constraints.add(acc_nonce == 0)

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F3947DEF4CF144679DA39C4C32BDC35681
        price = constraints.new_bitvec(256, name="price")
        constraints.add(price == 1000000000)

        value = constraints.new_bitvec(256, name="value")
        constraints.add(value == 1000000000000000000)

        gas = constraints.new_bitvec(256, name="gas")
        constraints.add(gas == 100000000000)

        data = constraints.new_array(index_max=34)
        constraints.add(
            data
            == b"\x124Vx\x9a\xbc\xde\xf0\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00$"
        )

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
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)),
            100000000000000000000000,
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6), unhexlify("600535600055")
        )
        # check storage
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x00)),
            0xBCDEF00000000000000000000000000000000000000000000000000024000000,
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
        self.assertEqual(solve(world.current_vm.gas), 99999979991)

    def test_calldatacopy_DataIndexTooHigh_return(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: calldatacopy_DataIndexTooHigh_return.json
        sha256sum: c4d8273ccd0d82d9667c5501bea79563329f85aca567eede9a07f6543709a63e
        Code:     PUSH1 0xff
                  PUSH32 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffa
                  PUSH1 0x0
                  CALLDATACOPY
                  PUSH1 0x0
                  MLOAD
                  PUSH1 0x0
                  SSTORE
                  MSIZE
                  PUSH1 0x0
                  RETURN
        """

        def solve(val):
            return self._solve(constraints, val)

        constraints = ConstraintSet()

        blocknumber = constraints.new_bitvec(256, name="blocknumber")
        constraints.add(blocknumber == 0)

        timestamp = constraints.new_bitvec(256, name="timestamp")
        constraints.add(timestamp == 1)

        difficulty = constraints.new_bitvec(256, name="difficulty")
        constraints.add(difficulty == 256)

        coinbase = constraints.new_bitvec(256, name="coinbase")
        constraints.add(coinbase == 244687034288125203496486448490407391986876152250)

        gaslimit = constraints.new_bitvec(256, name="gaslimit")
        constraints.add(gaslimit == 1000000)

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
            "60ff7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffa600037600051600055596000f3"
        )

        acc_balance = constraints.new_bitvec(
            256, name="balance_0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6"
        )
        constraints.add(acc_balance == 1000000000000000000)

        acc_nonce = constraints.new_bitvec(
            256, name="nonce_0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6"
        )
        constraints.add(acc_nonce == 0)

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F3947DEF4CF144679DA39C4C32BDC35681
        price = constraints.new_bitvec(256, name="price")
        constraints.add(price == 1000000000)

        value = constraints.new_bitvec(256, name="value")
        constraints.add(value == 1000000000000000000)

        gas = constraints.new_bitvec(256, name="gas")
        constraints.add(gas == 100000000000)

        data = constraints.new_array(index_max=17)
        constraints.add(data == b"\x124Vx\x90\xab\xcd\xef\x01#Eg\x89\n\xbc\xde\xf0")

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
                "60ff7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffa600037600051600055596000f3"
            ),
        )
        # check outs
        self.assertEqual(
            returndata,
            unhexlify(
                "00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000"
            ),
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
        self.assertEqual(solve(world.current_vm.gas), 99999994926)

    def test_calldatacopy1_return(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: calldatacopy1_return.json
        sha256sum: b7e6aa245f879323cdc9478104efdcad8c7bbe4f8312d67ad8e7f568ec9d537c
        Code:     PUSH1 0x1
                  PUSH1 0x1
                  PUSH1 0x0
                  CALLDATACOPY
                  PUSH1 0x0
                  MLOAD
                  PUSH1 0x0
                  SSTORE
                  MSIZE
                  PUSH1 0x0
                  RETURN
        """

        def solve(val):
            return self._solve(constraints, val)

        constraints = ConstraintSet()

        blocknumber = constraints.new_bitvec(256, name="blocknumber")
        constraints.add(blocknumber == 0)

        timestamp = constraints.new_bitvec(256, name="timestamp")
        constraints.add(timestamp == 1)

        difficulty = constraints.new_bitvec(256, name="difficulty")
        constraints.add(difficulty == 256)

        coinbase = constraints.new_bitvec(256, name="coinbase")
        constraints.add(coinbase == 244687034288125203496486448490407391986876152250)

        gaslimit = constraints.new_bitvec(256, name="gaslimit")
        constraints.add(gaslimit == 1000000)

        world = evm.EVMWorld(
            constraints,
            blocknumber=blocknumber,
            timestamp=timestamp,
            difficulty=difficulty,
            coinbase=coinbase,
            gaslimit=gaslimit,
        )

        acc_addr = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        acc_code = unhexlify("60016001600037600051600055596000f3")

        acc_balance = constraints.new_bitvec(
            256, name="balance_0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6"
        )
        constraints.add(acc_balance == 1000000000000000000)

        acc_nonce = constraints.new_bitvec(
            256, name="nonce_0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6"
        )
        constraints.add(acc_nonce == 0)

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F3947DEF4CF144679DA39C4C32BDC35681
        price = constraints.new_bitvec(256, name="price")
        constraints.add(price == 1000000000)

        value = constraints.new_bitvec(256, name="value")
        constraints.add(value == 1000000000000000000)

        gas = constraints.new_bitvec(256, name="gas")
        constraints.add(gas == 100000000000)

        data = constraints.new_array(index_max=17)
        constraints.add(data == b"\x124Vx\x90\xab\xcd\xef\x01#Eg\x89\n\xbc\xde\xf0")

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
            unhexlify("60016001600037600051600055596000f3"),
        )
        # check storage
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x00)),
            0x3400000000000000000000000000000000000000000000000000000000000000,
        )
        # check outs
        self.assertEqual(
            returndata,
            unhexlify("3400000000000000000000000000000000000000000000000000000000000000"),
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
        self.assertEqual(solve(world.current_vm.gas), 99999979968)

    def test_calldatacopyZeroMemExpansion(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: calldatacopyZeroMemExpansion.json
        sha256sum: dfb6e3a5fa584962ec2c1b2de3c6a948e04fc307c69744e80de7125320b7278d
        Code:     PUSH1 0x0
                  PUSH1 0x0
                  PUSH1 0x0
                  CALLDATACOPY
                  PUSH1 0x0
                  MLOAD
                  PUSH1 0x0
                  SSTORE
        """

        def solve(val):
            return self._solve(constraints, val)

        constraints = ConstraintSet()

        blocknumber = constraints.new_bitvec(256, name="blocknumber")
        constraints.add(blocknumber == 0)

        timestamp = constraints.new_bitvec(256, name="timestamp")
        constraints.add(timestamp == 1)

        difficulty = constraints.new_bitvec(256, name="difficulty")
        constraints.add(difficulty == 256)

        coinbase = constraints.new_bitvec(256, name="coinbase")
        constraints.add(coinbase == 244687034288125203496486448490407391986876152250)

        gaslimit = constraints.new_bitvec(256, name="gaslimit")
        constraints.add(gaslimit == 1000000)

        world = evm.EVMWorld(
            constraints,
            blocknumber=blocknumber,
            timestamp=timestamp,
            difficulty=difficulty,
            coinbase=coinbase,
            gaslimit=gaslimit,
        )

        acc_addr = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        acc_code = unhexlify("60006000600037600051600055")

        acc_balance = constraints.new_bitvec(
            256, name="balance_0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6"
        )
        constraints.add(acc_balance == 100000000000000000000000)

        acc_nonce = constraints.new_bitvec(
            256, name="nonce_0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6"
        )
        constraints.add(acc_nonce == 0)

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F3947DEF4CF144679DA39C4C32BDC35681
        price = constraints.new_bitvec(256, name="price")
        constraints.add(price == 1000000000)

        value = constraints.new_bitvec(256, name="value")
        constraints.add(value == 1000000000000000000)

        gas = constraints.new_bitvec(256, name="gas")
        constraints.add(gas == 100000000000)

        data = constraints.new_array(index_max=17)
        constraints.add(data == b"\x124Vx\x90\xab\xcd\xef\x01#Eg\x89\n\xbc\xde\xf0")

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
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)),
            100000000000000000000000,
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6),
            unhexlify("60006000600037600051600055"),
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
        self.assertEqual(solve(world.current_vm.gas), 99999994976)

    def test_calldatacopy_DataIndexTooHigh2(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: calldatacopy_DataIndexTooHigh2.json
        sha256sum: 381db3e53b756d37a287d886b8ffac894313e17ce27cde745e1f5f36779567d1
        Code:     PUSH1 0x9
                  PUSH32 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffa
                  PUSH1 0x0
                  CALLDATACOPY
                  PUSH1 0x0
                  MLOAD
                  PUSH1 0x0
                  SSTORE
        """

        def solve(val):
            return self._solve(constraints, val)

        constraints = ConstraintSet()

        blocknumber = constraints.new_bitvec(256, name="blocknumber")
        constraints.add(blocknumber == 0)

        timestamp = constraints.new_bitvec(256, name="timestamp")
        constraints.add(timestamp == 1)

        difficulty = constraints.new_bitvec(256, name="difficulty")
        constraints.add(difficulty == 256)

        coinbase = constraints.new_bitvec(256, name="coinbase")
        constraints.add(coinbase == 244687034288125203496486448490407391986876152250)

        gaslimit = constraints.new_bitvec(256, name="gaslimit")
        constraints.add(gaslimit == 1000000)

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
            "60097ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffa600037600051600055"
        )

        acc_balance = constraints.new_bitvec(
            256, name="balance_0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6"
        )
        constraints.add(acc_balance == 100000000000000000000000)

        acc_nonce = constraints.new_bitvec(
            256, name="nonce_0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6"
        )
        constraints.add(acc_nonce == 0)

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F3947DEF4CF144679DA39C4C32BDC35681
        price = constraints.new_bitvec(256, name="price")
        constraints.add(price == 1000000000)

        value = constraints.new_bitvec(256, name="value")
        constraints.add(value == 1000000000000000000)

        gas = constraints.new_bitvec(256, name="gas")
        constraints.add(gas == 100000000000)

        data = constraints.new_array(index_max=17)
        constraints.add(data == b"\x124Vx\x90\xab\xcd\xef\x01#Eg\x89\n\xbc\xde\xf0")

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
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)),
            100000000000000000000000,
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6),
            unhexlify(
                "60097ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffa600037600051600055"
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
        self.assertEqual(solve(world.current_vm.gas), 99999994973)

    def test_calldatacopy2_return(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: calldatacopy2_return.json
        sha256sum: a26586fa1b2ee81e7653875490bdedd495076bb775ebcff9d6c2112eaa8babde
        Code:     PUSH1 0x0
                  PUSH1 0x1
                  PUSH1 0x0
                  CALLDATACOPY
                  PUSH1 0x0
                  MLOAD
                  PUSH1 0x0
                  SSTORE
                  MSIZE
                  PUSH1 0x0
                  RETURN
        """

        def solve(val):
            return self._solve(constraints, val)

        constraints = ConstraintSet()

        blocknumber = constraints.new_bitvec(256, name="blocknumber")
        constraints.add(blocknumber == 0)

        timestamp = constraints.new_bitvec(256, name="timestamp")
        constraints.add(timestamp == 1)

        difficulty = constraints.new_bitvec(256, name="difficulty")
        constraints.add(difficulty == 256)

        coinbase = constraints.new_bitvec(256, name="coinbase")
        constraints.add(coinbase == 244687034288125203496486448490407391986876152250)

        gaslimit = constraints.new_bitvec(256, name="gaslimit")
        constraints.add(gaslimit == 1000000)

        world = evm.EVMWorld(
            constraints,
            blocknumber=blocknumber,
            timestamp=timestamp,
            difficulty=difficulty,
            coinbase=coinbase,
            gaslimit=gaslimit,
        )

        acc_addr = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        acc_code = unhexlify("60006001600037600051600055596000f3")

        acc_balance = constraints.new_bitvec(
            256, name="balance_0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6"
        )
        constraints.add(acc_balance == 1000000000000000000)

        acc_nonce = constraints.new_bitvec(
            256, name="nonce_0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6"
        )
        constraints.add(acc_nonce == 0)

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F3947DEF4CF144679DA39C4C32BDC35681
        price = constraints.new_bitvec(256, name="price")
        constraints.add(price == 1000000000)

        value = constraints.new_bitvec(256, name="value")
        constraints.add(value == 1000000000000000000)

        gas = constraints.new_bitvec(256, name="gas")
        constraints.add(gas == 100000000000)

        data = constraints.new_array(index_max=17)
        constraints.add(data == b"\x124Vx\x90\xab\xcd\xef\x01#Eg\x89\n\xbc\xde\xf0")

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
            unhexlify("60006001600037600051600055596000f3"),
        )
        # check outs
        self.assertEqual(
            returndata,
            unhexlify("0000000000000000000000000000000000000000000000000000000000000000"),
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
        self.assertEqual(solve(world.current_vm.gas), 99999994971)

    def test_calldataloadSizeTooHighPartial(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: calldataloadSizeTooHighPartial.json
        sha256sum: a2899760b2ca03b1f32c69b62a70751e2be4fc9b880d97e86f151b066116221a
        Code:     PUSH1 0xa
                  CALLDATALOAD
                  PUSH1 0x0
                  SSTORE
        """

        def solve(val):
            return self._solve(constraints, val)

        constraints = ConstraintSet()

        blocknumber = constraints.new_bitvec(256, name="blocknumber")
        constraints.add(blocknumber == 0)

        timestamp = constraints.new_bitvec(256, name="timestamp")
        constraints.add(timestamp == 1)

        difficulty = constraints.new_bitvec(256, name="difficulty")
        constraints.add(difficulty == 256)

        coinbase = constraints.new_bitvec(256, name="coinbase")
        constraints.add(coinbase == 244687034288125203496486448490407391986876152250)

        gaslimit = constraints.new_bitvec(256, name="gaslimit")
        constraints.add(gaslimit == 1000000)

        world = evm.EVMWorld(
            constraints,
            blocknumber=blocknumber,
            timestamp=timestamp,
            difficulty=difficulty,
            coinbase=coinbase,
            gaslimit=gaslimit,
        )

        acc_addr = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        acc_code = unhexlify("600a35600055")

        acc_balance = constraints.new_bitvec(
            256, name="balance_0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6"
        )
        constraints.add(acc_balance == 100000000000000000000000)

        acc_nonce = constraints.new_bitvec(
            256, name="nonce_0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6"
        )
        constraints.add(acc_nonce == 0)

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F3947DEF4CF144679DA39C4C32BDC35681
        price = constraints.new_bitvec(256, name="price")
        constraints.add(price == 1000000000)

        value = constraints.new_bitvec(256, name="value")
        constraints.add(value == 1000000000000000000)

        gas = constraints.new_bitvec(256, name="gas")
        constraints.add(gas == 100000000000)

        data = constraints.new_array(index_max=31)
        constraints.add(
            data
            == b"\x124Vx\x9a\xbc\xde\xf0\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00$"
        )

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
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)),
            100000000000000000000000,
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6), unhexlify("600a35600055")
        )
        # check storage
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x00)),
            0x240000000000000000000000,
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
        self.assertEqual(solve(world.current_vm.gas), 99999979991)

    def test_calldatasize2(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: calldatasize2.json
        sha256sum: ad21f9b77011891fdb9f015a147c3686e36932a23e3cc8390fb645208fa52b45
        Code:     CALLDATASIZE
                  PUSH1 0x0
                  SSTORE
        """

        def solve(val):
            return self._solve(constraints, val)

        constraints = ConstraintSet()

        blocknumber = constraints.new_bitvec(256, name="blocknumber")
        constraints.add(blocknumber == 0)

        timestamp = constraints.new_bitvec(256, name="timestamp")
        constraints.add(timestamp == 1)

        difficulty = constraints.new_bitvec(256, name="difficulty")
        constraints.add(difficulty == 256)

        coinbase = constraints.new_bitvec(256, name="coinbase")
        constraints.add(coinbase == 244687034288125203496486448490407391986876152250)

        gaslimit = constraints.new_bitvec(256, name="gaslimit")
        constraints.add(gaslimit == 1000000)

        world = evm.EVMWorld(
            constraints,
            blocknumber=blocknumber,
            timestamp=timestamp,
            difficulty=difficulty,
            coinbase=coinbase,
            gaslimit=gaslimit,
        )

        acc_addr = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        acc_code = unhexlify("36600055")

        acc_balance = constraints.new_bitvec(
            256, name="balance_0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6"
        )
        constraints.add(acc_balance == 100000000000000000000000)

        acc_nonce = constraints.new_bitvec(
            256, name="nonce_0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6"
        )
        constraints.add(acc_nonce == 0)

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F3947DEF4CF144679DA39C4C32BDC35681
        price = constraints.new_bitvec(256, name="price")
        constraints.add(price == 1000000000)

        value = constraints.new_bitvec(256, name="value")
        constraints.add(value == 1000000000000000000)

        gas = constraints.new_bitvec(256, name="gas")
        constraints.add(gas == 100000000000)

        data = constraints.new_array(index_max=33)
        constraints.add(
            data
            == b"#\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00#"
        )

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
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)),
            100000000000000000000000,
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6), unhexlify("36600055")
        )
        # check storage
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x00)), 0x21
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
        self.assertEqual(solve(world.current_vm.gas), 99999979995)

    def test_calldataload0(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: calldataload0.json
        sha256sum: cfb745bb3e23954a86c5adf5aac0f51d8001aabdbc28c34b8dafe850569a2df2
        Code:     PUSH1 0x0
                  CALLDATALOAD
                  PUSH1 0x0
                  SSTORE
        """

        def solve(val):
            return self._solve(constraints, val)

        constraints = ConstraintSet()

        blocknumber = constraints.new_bitvec(256, name="blocknumber")
        constraints.add(blocknumber == 0)

        timestamp = constraints.new_bitvec(256, name="timestamp")
        constraints.add(timestamp == 1)

        difficulty = constraints.new_bitvec(256, name="difficulty")
        constraints.add(difficulty == 256)

        coinbase = constraints.new_bitvec(256, name="coinbase")
        constraints.add(coinbase == 244687034288125203496486448490407391986876152250)

        gaslimit = constraints.new_bitvec(256, name="gaslimit")
        constraints.add(gaslimit == 1000000)

        world = evm.EVMWorld(
            constraints,
            blocknumber=blocknumber,
            timestamp=timestamp,
            difficulty=difficulty,
            coinbase=coinbase,
            gaslimit=gaslimit,
        )

        acc_addr = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        acc_code = unhexlify("600035600055")

        acc_balance = constraints.new_bitvec(
            256, name="balance_0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6"
        )
        constraints.add(acc_balance == 100000000000000000000000)

        acc_nonce = constraints.new_bitvec(
            256, name="nonce_0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6"
        )
        constraints.add(acc_nonce == 0)

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F3947DEF4CF144679DA39C4C32BDC35681
        price = constraints.new_bitvec(256, name="price")
        constraints.add(price == 1000000000)

        value = constraints.new_bitvec(256, name="value")
        constraints.add(value == 1000000000000000000)

        gas = constraints.new_bitvec(256, name="gas")
        constraints.add(gas == 100000000000)

        data = constraints.new_array(index_max=2)
        constraints.add(data == b"%`")

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
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)),
            100000000000000000000000,
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6), unhexlify("600035600055")
        )
        # check storage
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x00)),
            0x2560000000000000000000000000000000000000000000000000000000000000,
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
        self.assertEqual(solve(world.current_vm.gas), 99999979991)

    def test_codesize(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: codesize.json
        sha256sum: 5704de4f0d6c6b328fccffb5c397854c3c5c0064aee3eec0277a60d8920e5051
        Code:     CODESIZE
                  PUSH1 0x0
                  SSTORE
        """

        def solve(val):
            return self._solve(constraints, val)

        constraints = ConstraintSet()

        blocknumber = constraints.new_bitvec(256, name="blocknumber")
        constraints.add(blocknumber == 0)

        timestamp = constraints.new_bitvec(256, name="timestamp")
        constraints.add(timestamp == 1)

        difficulty = constraints.new_bitvec(256, name="difficulty")
        constraints.add(difficulty == 256)

        coinbase = constraints.new_bitvec(256, name="coinbase")
        constraints.add(coinbase == 244687034288125203496486448490407391986876152250)

        gaslimit = constraints.new_bitvec(256, name="gaslimit")
        constraints.add(gaslimit == 1000000)

        world = evm.EVMWorld(
            constraints,
            blocknumber=blocknumber,
            timestamp=timestamp,
            difficulty=difficulty,
            coinbase=coinbase,
            gaslimit=gaslimit,
        )

        acc_addr = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        acc_code = unhexlify("38600055")

        acc_balance = constraints.new_bitvec(
            256, name="balance_0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6"
        )
        constraints.add(acc_balance == 100000000000000000000000)

        acc_nonce = constraints.new_bitvec(
            256, name="nonce_0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6"
        )
        constraints.add(acc_nonce == 0)

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F3947DEF4CF144679DA39C4C32BDC35681
        price = constraints.new_bitvec(256, name="price")
        constraints.add(price == 1000000000)

        value = constraints.new_bitvec(256, name="value")
        constraints.add(value == 1000000000000000000)

        gas = constraints.new_bitvec(256, name="gas")
        constraints.add(gas == 100000000000)

        data = constraints.new_array(index_max=17)
        constraints.add(data == b"\x124Vx\x90\xab\xcd\xef\x01#Eg\x89\n\xbc\xde\xf0")

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
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)),
            100000000000000000000000,
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6), unhexlify("38600055")
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
        self.assertEqual(solve(world.current_vm.gas), 99999979995)

    def test_address1(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: address1.json
        sha256sum: fd14b93c0b05baf12caa61c62c65cf77bb02300d7f0e4737947b3512981e1a3d
        Code:     ADDRESS
                  PUSH1 0x0
                  SSTORE
        """

        def solve(val):
            return self._solve(constraints, val)

        constraints = ConstraintSet()

        blocknumber = constraints.new_bitvec(256, name="blocknumber")
        constraints.add(blocknumber == 0)

        timestamp = constraints.new_bitvec(256, name="timestamp")
        constraints.add(timestamp == 1)

        difficulty = constraints.new_bitvec(256, name="difficulty")
        constraints.add(difficulty == 256)

        coinbase = constraints.new_bitvec(256, name="coinbase")
        constraints.add(coinbase == 244687034288125203496486448490407391986876152250)

        gaslimit = constraints.new_bitvec(256, name="gaslimit")
        constraints.add(gaslimit == 1000000)

        world = evm.EVMWorld(
            constraints,
            blocknumber=blocknumber,
            timestamp=timestamp,
            difficulty=difficulty,
            coinbase=coinbase,
            gaslimit=gaslimit,
        )

        acc_addr = 0xCD1722F3947DEF4CF144679DA39C4C32BDC35681
        acc_code = unhexlify("30600055")

        acc_balance = constraints.new_bitvec(
            256, name="balance_0xcd1722f3947def4cf144679da39c4c32bdc35681"
        )
        constraints.add(acc_balance == 100000000000000000000000)

        acc_nonce = constraints.new_bitvec(
            256, name="nonce_0xcd1722f3947def4cf144679da39c4c32bdc35681"
        )
        constraints.add(acc_nonce == 0)

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xCD1722F3947DEF4CF144679DA39C4C32BDC35681
        caller = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        price = constraints.new_bitvec(256, name="price")
        constraints.add(price == 1000000000)

        value = constraints.new_bitvec(256, name="value")
        constraints.add(value == 1000000000000000000)

        gas = constraints.new_bitvec(256, name="gas")
        constraints.add(gas == 100000000000)

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
        self.assertEqual(
            world.get_code(0xCD1722F3947DEF4CF144679DA39C4C32BDC35681), unhexlify("30600055")
        )
        # check storage
        self.assertEqual(
            solve(world.get_storage_data(0xCD1722F3947DEF4CF144679DA39C4C32BDC35681, 0x00)),
            0xCD1722F3947DEF4CF144679DA39C4C32BDC35681,
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
        self.assertEqual(solve(world.current_vm.gas), 99999979995)

    def test_calldatacopy1(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: calldatacopy1.json
        sha256sum: 3e863533282cd4f0dea6a8e6dd00799828ad59478560079a085b16fbf98b829e
        Code:     PUSH1 0x1
                  PUSH1 0x1
                  PUSH1 0x0
                  CALLDATACOPY
                  PUSH1 0x0
                  MLOAD
                  PUSH1 0x0
                  SSTORE
        """

        def solve(val):
            return self._solve(constraints, val)

        constraints = ConstraintSet()

        blocknumber = constraints.new_bitvec(256, name="blocknumber")
        constraints.add(blocknumber == 0)

        timestamp = constraints.new_bitvec(256, name="timestamp")
        constraints.add(timestamp == 1)

        difficulty = constraints.new_bitvec(256, name="difficulty")
        constraints.add(difficulty == 256)

        coinbase = constraints.new_bitvec(256, name="coinbase")
        constraints.add(coinbase == 244687034288125203496486448490407391986876152250)

        gaslimit = constraints.new_bitvec(256, name="gaslimit")
        constraints.add(gaslimit == 1000000)

        world = evm.EVMWorld(
            constraints,
            blocknumber=blocknumber,
            timestamp=timestamp,
            difficulty=difficulty,
            coinbase=coinbase,
            gaslimit=gaslimit,
        )

        acc_addr = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        acc_code = unhexlify("60016001600037600051600055")

        acc_balance = constraints.new_bitvec(
            256, name="balance_0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6"
        )
        constraints.add(acc_balance == 100000000000000000000000)

        acc_nonce = constraints.new_bitvec(
            256, name="nonce_0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6"
        )
        constraints.add(acc_nonce == 0)

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        caller = 0xCD1722F3947DEF4CF144679DA39C4C32BDC35681
        price = constraints.new_bitvec(256, name="price")
        constraints.add(price == 1000000000)

        value = constraints.new_bitvec(256, name="value")
        constraints.add(value == 1000000000000000000)

        gas = constraints.new_bitvec(256, name="gas")
        constraints.add(gas == 100000000000)

        data = constraints.new_array(index_max=17)
        constraints.add(data == b"\x124Vx\x90\xab\xcd\xef\x01#Eg\x89\n\xbc\xde\xf0")

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
            solve(world.get_balance(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6)),
            100000000000000000000000,
        )
        self.assertEqual(
            world.get_code(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6),
            unhexlify("60016001600037600051600055"),
        )
        # check storage
        self.assertEqual(
            solve(world.get_storage_data(0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6, 0x00)),
            0x3400000000000000000000000000000000000000000000000000000000000000,
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
        self.assertEqual(solve(world.current_vm.gas), 99999979973)


if __name__ == "__main__":
    unittest.main()
