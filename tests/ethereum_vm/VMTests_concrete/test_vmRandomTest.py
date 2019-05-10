"""DO NOT MODIFY: Tests generated from `VMTests/vmRandomTest` with make_VMTests.py"""
import unittest
from binascii import unhexlify

import rlp
import sha3
from rlp.sedes import (
    CountableList,
    BigEndianInt,
    Binary,
)

from manticore.core.smtlib import ConstraintSet, Z3Solver  # Ignore unused import in non-symbolic tests!
from manticore.core.smtlib.visitors import to_constant
from manticore.platforms import evm
from manticore.utils import config
from manticore.core.state import Concretize



class Log(rlp.Serializable):
    fields = [
        ('address', Binary.fixed_length(20, allow_empty=True)),
        ('topics', CountableList(BigEndianInt(32))),
        ('data', Binary())
    ]


class EVMTest_vmRandomTest(unittest.TestCase):
    # https://nose.readthedocs.io/en/latest/doc_tests/test_multiprocess/multiprocess.html#controlling-distribution
    _multiprocess_can_split_ = True
    # https://docs.python.org/3.7/library/unittest.html#unittest.TestCase.maxDiff
    maxDiff = None

    SAVED_DEFAULT_FORK = evm.DEFAULT_FORK

    @classmethod
    def setUpClass(cls):
        consts = config.get_group('evm')
        consts.oog = 'pedantic'
        evm.DEFAULT_FORK = 'frontier'

    @classmethod
    def tearDownClass(cls):
        evm.DEFAULT_FORK = cls.SAVED_DEFAULT_FORK

    def _test_run(self, world):
        result = None
        returndata = b''
        try:
            while True:
                try:
                    world.current_vm.execute()
                except Concretize as e:
                    value = self._solve(world.constraints, e.expression)
                    class fake_state:pass
                    fake_state = fake_state()
                    fake_state.platform = world
                    e.setstate(fake_state, value)
        except evm.EndTx as e:
            result = e.result
            if result in ('RETURN', 'REVERT'):
                returndata = self._solve(world.constraints, e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        return result, returndata

    def _solve(self, constraints, val):
        results = Z3Solver.instance().get_all_values(constraints, val, maxcnt=3)
        # We constrain all values to single values!
        self.assertEqual(len(results), 1)
        return results[0]


    def test_201503110206PYTHON(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: 201503110206PYTHON.json
        sha256sum: d02dd686767e9a3f281f4dce40244cbe23a022eae7a3e8cc3dd2e747b889500a
        Code:     BLOCKHASH
                  GASLIMIT
                  BLOCKHASH
                  COINBASE
                  GASLIMIT
                  GASLIMIT
                  DIFFICULTY
                  COINBASE
                  CALLVALUE
                  CODECOPY
                  DUP8
                  SELFDESTRUCT
                  CALLDATACOPY
                  CALLDATALOAD
                  DIV
                  ADDRESS
                  SSTORE
        """    
    
        def solve(val):
            """
            Those tests are **auto-generated** and `solve` is used in symbolic tests.
            So yes, this returns just val; it makes it easier to generate tests like this.
            """
            return to_constant(val)

        constraints = ConstraintSet()

        blocknumber = 300
        timestamp = 2
        difficulty = 115792089237316195423570985008687907853269984665640564039457584007913129639935
        coinbase = 244687034288125203496486448490407391986876152250
        gaslimit = 1000000
        world = evm.EVMWorld(constraints, blocknumber=blocknumber, timestamp=timestamp, difficulty=difficulty,
                             coinbase=coinbase, gaslimit=gaslimit)
    
        acc_addr = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        acc_code = unhexlify('4045404145454441343987ff3735043055')
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        caller = 0xcd1722f3947def4cf144679da39c4c32bdc35681
        price = 0x5af3107a4000
        value = 1000000000000000000
        gas = 10000
        data = ''
        # open a fake tx, no funds send
        world._open_transaction('CALL', address, price, data, caller, value, gas=gas)

        # This variable might seem redundant in some tests - don't forget it is auto generated
        # and there are cases in which we need it ;)
        result, returndata = self._test_run(world)

        # World sanity checks - those should not change, right?
        self.assertEqual(solve(world.block_number()), 300)
        self.assertEqual(solve(world.block_gaslimit()), 1000000)
        self.assertEqual(solve(world.block_timestamp()), 2)
        self.assertEqual(solve(world.block_difficulty()), 115792089237316195423570985008687907853269984665640564039457584007913129639935)
        self.assertEqual(solve(world.block_coinbase()), 0x2adc25665018aa1fe0e6bc666dac8fc2697ff9ba)

        # If test end in exception check it here
        self.assertTrue(result == 'THROW')

    def test_201503112218PYTHON(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: 201503112218PYTHON.json
        sha256sum: cbd7e0e94cc25d26f381b86d2808304264910c18affd48aad6bbe888929e4207
        Code:     BLOCKHASH
                  COINBASE
        """    
    
        def solve(val):
            """
            Those tests are **auto-generated** and `solve` is used in symbolic tests.
            So yes, this returns just val; it makes it easier to generate tests like this.
            """
            return to_constant(val)

        constraints = ConstraintSet()

        blocknumber = 300
        timestamp = 2
        difficulty = 115792089237316195423570985008687907853269984665640564039457584007913129639935
        coinbase = 244687034288125203496486448490407391986876152250
        gaslimit = 1000000
        world = evm.EVMWorld(constraints, blocknumber=blocknumber, timestamp=timestamp, difficulty=difficulty,
                             coinbase=coinbase, gaslimit=gaslimit)
    
        acc_addr = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        acc_code = unhexlify('4041')
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        caller = 0xcd1722f3947def4cf144679da39c4c32bdc35681
        price = 0x5af3107a4000
        value = 1000000000000000000
        gas = 10000
        data = ''
        # open a fake tx, no funds send
        world._open_transaction('CALL', address, price, data, caller, value, gas=gas)

        # This variable might seem redundant in some tests - don't forget it is auto generated
        # and there are cases in which we need it ;)
        result, returndata = self._test_run(world)

        # World sanity checks - those should not change, right?
        self.assertEqual(solve(world.block_number()), 300)
        self.assertEqual(solve(world.block_gaslimit()), 1000000)
        self.assertEqual(solve(world.block_timestamp()), 2)
        self.assertEqual(solve(world.block_difficulty()), 115792089237316195423570985008687907853269984665640564039457584007913129639935)
        self.assertEqual(solve(world.block_coinbase()), 0x2adc25665018aa1fe0e6bc666dac8fc2697ff9ba)

        # If test end in exception check it here
        self.assertTrue(result == 'THROW')

    def test_201503111844PYTHON(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: 201503111844PYTHON.json
        sha256sum: 75bc0568cd5fe782e030391083658cdcbac61e32d6f0b1bdce9286ee7fd6d75e
        Code:     
        """    
    
        def solve(val):
            """
            Those tests are **auto-generated** and `solve` is used in symbolic tests.
            So yes, this returns just val; it makes it easier to generate tests like this.
            """
            return to_constant(val)

        constraints = ConstraintSet()

        blocknumber = 300
        timestamp = 2
        difficulty = 115792089237316195423570985008687907853269984665640564039457584007913129639935
        coinbase = 244687034288125203496486448490407391986876152250
        gaslimit = 1000000
        world = evm.EVMWorld(constraints, blocknumber=blocknumber, timestamp=timestamp, difficulty=difficulty,
                             coinbase=coinbase, gaslimit=gaslimit)
    
        acc_addr = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        acc_code = unhexlify('65424555')
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        caller = 0xcd1722f3947def4cf144679da39c4c32bdc35681
        price = 0x5af3107a4000
        value = 1000000000000000000
        gas = 10000
        data = ''
        # open a fake tx, no funds send
        world._open_transaction('CALL', address, price, data, caller, value, gas=gas)

        # This variable might seem redundant in some tests - don't forget it is auto generated
        # and there are cases in which we need it ;)
        result, returndata = self._test_run(world)

        # World sanity checks - those should not change, right?
        self.assertEqual(solve(world.block_number()), 300)
        self.assertEqual(solve(world.block_gaslimit()), 1000000)
        self.assertEqual(solve(world.block_timestamp()), 2)
        self.assertEqual(solve(world.block_difficulty()), 115792089237316195423570985008687907853269984665640564039457584007913129639935)
        self.assertEqual(solve(world.block_coinbase()), 0x2adc25665018aa1fe0e6bc666dac8fc2697ff9ba)

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 0)
        self.assertEqual(solve(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('65424555'))
        # check outs
        self.assertEqual(returndata, unhexlify(''))
        # check logs
        logs = [Log(unhexlify('{:040x}'.format(l.address)), l.topics, solve(l.memlog)) for l in world.logs]
        data = rlp.encode(logs)
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')

        # test used gas
        self.assertEqual(solve(world.current_vm.gas), 9997)

    def test_201503102320PYTHON(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: 201503102320PYTHON.json
        sha256sum: 612078317eb4f60643c39c4c0d2ee8e9c0c853ed5188d437d811cba47fe9e26f
        Code:     NUMBER
                  NUMBER
                  TIMESTAMP
                  DIFFICULTY
                  TIMESTAMP
                  DIFFICULTY
                  GASLIMIT
                  GASLIMIT
                  SWAP8
        """    
    
        def solve(val):
            """
            Those tests are **auto-generated** and `solve` is used in symbolic tests.
            So yes, this returns just val; it makes it easier to generate tests like this.
            """
            return to_constant(val)

        constraints = ConstraintSet()

        blocknumber = 300
        timestamp = 2
        difficulty = 115792089237316195423570985008687907853269984665640564039457584007913129639935
        coinbase = 244687034288125203496486448490407391986876152250
        gaslimit = 1000000
        world = evm.EVMWorld(constraints, blocknumber=blocknumber, timestamp=timestamp, difficulty=difficulty,
                             coinbase=coinbase, gaslimit=gaslimit)
    
        acc_addr = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        acc_code = unhexlify('434342444244454597')
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        caller = 0xcd1722f3947def4cf144679da39c4c32bdc35681
        price = 0x5af3107a4000
        value = 1000000000000000000
        gas = 10000
        data = ''
        # open a fake tx, no funds send
        world._open_transaction('CALL', address, price, data, caller, value, gas=gas)

        # This variable might seem redundant in some tests - don't forget it is auto generated
        # and there are cases in which we need it ;)
        result, returndata = self._test_run(world)

        # World sanity checks - those should not change, right?
        self.assertEqual(solve(world.block_number()), 300)
        self.assertEqual(solve(world.block_gaslimit()), 1000000)
        self.assertEqual(solve(world.block_timestamp()), 2)
        self.assertEqual(solve(world.block_difficulty()), 115792089237316195423570985008687907853269984665640564039457584007913129639935)
        self.assertEqual(solve(world.block_coinbase()), 0x2adc25665018aa1fe0e6bc666dac8fc2697ff9ba)

        # If test end in exception check it here
        self.assertTrue(result == 'THROW')

    def test_201503110219PYTHON(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: 201503110219PYTHON.json
        sha256sum: e153bd49bafe6f1e398ddaeb35a9f0493d823b36c3823908211bf371ec95cb1f
        Code:     BLOCKHASH
                  BLOCKHASH
                  GASLIMIT
                  SWAP2
                  NUMBER
                  BLOCKHASH
                  COINBASE
                  DIFFICULTY
                  DUP1
                  SWAP8
                  MSIZE
                  DUP9
        """    
    
        def solve(val):
            """
            Those tests are **auto-generated** and `solve` is used in symbolic tests.
            So yes, this returns just val; it makes it easier to generate tests like this.
            """
            return to_constant(val)

        constraints = ConstraintSet()

        blocknumber = 300
        timestamp = 2
        difficulty = 115792089237316195423570985008687907853269984665640564039457584007913129639935
        coinbase = 244687034288125203496486448490407391986876152250
        gaslimit = 1000000
        world = evm.EVMWorld(constraints, blocknumber=blocknumber, timestamp=timestamp, difficulty=difficulty,
                             coinbase=coinbase, gaslimit=gaslimit)
    
        acc_addr = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        acc_code = unhexlify('4040459143404144809759886d608f')
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        caller = 0xcd1722f3947def4cf144679da39c4c32bdc35681
        price = 0x5af3107a4000
        value = 1000000000000000000
        gas = 10000
        data = ''
        # open a fake tx, no funds send
        world._open_transaction('CALL', address, price, data, caller, value, gas=gas)

        # This variable might seem redundant in some tests - don't forget it is auto generated
        # and there are cases in which we need it ;)
        result, returndata = self._test_run(world)

        # World sanity checks - those should not change, right?
        self.assertEqual(solve(world.block_number()), 300)
        self.assertEqual(solve(world.block_gaslimit()), 1000000)
        self.assertEqual(solve(world.block_timestamp()), 2)
        self.assertEqual(solve(world.block_difficulty()), 115792089237316195423570985008687907853269984665640564039457584007913129639935)
        self.assertEqual(solve(world.block_coinbase()), 0x2adc25665018aa1fe0e6bc666dac8fc2697ff9ba)

        # If test end in exception check it here
        self.assertTrue(result == 'THROW')

    def test_201503110346PYTHON_PUSH24(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: 201503110346PYTHON_PUSH24.json
        sha256sum: 0f512fa3c9cf0e24e246ca46e8e072745df14f1cdfc8fcf6d201aba5e55f7932
        Code:     
        """    
    
        def solve(val):
            """
            Those tests are **auto-generated** and `solve` is used in symbolic tests.
            So yes, this returns just val; it makes it easier to generate tests like this.
            """
            return to_constant(val)

        constraints = ConstraintSet()

        blocknumber = 300
        timestamp = 2
        difficulty = 115792089237316195423570985008687907853269984665640564039457584007913129639935
        coinbase = 244687034288125203496486448490407391986876152250
        gaslimit = 1000000
        world = evm.EVMWorld(constraints, blocknumber=blocknumber, timestamp=timestamp, difficulty=difficulty,
                             coinbase=coinbase, gaslimit=gaslimit)
    
        acc_addr = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        acc_code = unhexlify('7745414245403745f31387900a8d55')
        acc_balance = 1000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        caller = 0xcd1722f3947def4cf144679da39c4c32bdc35681
        price = 0x5af3107a4000
        value = 1000000000000000000
        gas = 10000
        data = ''
        # open a fake tx, no funds send
        world._open_transaction('CALL', address, price, data, caller, value, gas=gas)

        # This variable might seem redundant in some tests - don't forget it is auto generated
        # and there are cases in which we need it ;)
        result, returndata = self._test_run(world)

        # World sanity checks - those should not change, right?
        self.assertEqual(solve(world.block_number()), 300)
        self.assertEqual(solve(world.block_gaslimit()), 1000000)
        self.assertEqual(solve(world.block_timestamp()), 2)
        self.assertEqual(solve(world.block_difficulty()), 115792089237316195423570985008687907853269984665640564039457584007913129639935)
        self.assertEqual(solve(world.block_coinbase()), 0x2adc25665018aa1fe0e6bc666dac8fc2697ff9ba)

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 0)
        self.assertEqual(solve(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('7745414245403745f31387900a8d55'))
        # check outs
        self.assertEqual(returndata, unhexlify(''))
        # check logs
        logs = [Log(unhexlify('{:040x}'.format(l.address)), l.topics, solve(l.memlog)) for l in world.logs]
        data = rlp.encode(logs)
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')

        # test used gas
        self.assertEqual(solve(world.current_vm.gas), 9997)


if __name__ == '__main__':
    unittest.main()
