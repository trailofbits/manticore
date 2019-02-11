"""DO NOT MODIFY: Tests generated from `VMTests/vmBlockInfoTest` with make_VMTests.py"""
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


class Log(rlp.Serializable):
    fields = [
        ('address', Binary.fixed_length(20, allow_empty=True)),
        ('topics', CountableList(BigEndianInt(32))),
        ('data', Binary())
    ]


class EVMTest_vmBlockInfoTest(unittest.TestCase):
    # https://nose.readthedocs.io/en/latest/doc_tests/test_multiprocess/multiprocess.html#controlling-distribution
    _multiprocess_can_split_ = True
    # https://docs.python.org/3.7/library/unittest.html#unittest.TestCase.maxDiff
    maxDiff = None

    SAVED_DEFAULT_FORK = evm.DEFAULT_FORK

    @classmethod
    def setUpClass(cls):
        evm.DEFAULT_FORK = 'frontier'

    @classmethod
    def tearDownClass(cls):
        evm.DEFAULT_FORK = cls.SAVED_DEFAULT_FORK

    def test_gaslimit(self):
        """
        Textcase taken from https://github.com/ethereum/tests
        File: gaslimit.json
        sha256sum: 656f33ecf7d1b15db096476b9125b969f5e3d312c85db39893a4d8f5fba57d7f
        Code:     GASLIMIT
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
        world = evm.EVMWorld(constraints, blocknumber=blocknumber, timestamp=timestamp, difficulty=difficulty,
                             coinbase=coinbase, gaslimit=gaslimit)
    
        acc_addr = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        acc_code = unhexlify('45600055')
        acc_balance = 100000000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        caller = 0xcd1722f3947def4cf144679da39c4c32bdc35681
        price = 0x5af3107a4000
        value = 1000000000000000000
        gas = 100000
        data = ''
        # open a fake tx, no funds send
        world._open_transaction('CALL', address, price, data, caller, value, gas=gas)

        # This variable might seem redundant in some tests - don't forget it is auto generated
        # and there are cases in which we need it ;)
        result = None
        returndata = b''
        try:
            while True:
                world.current_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if result in ('RETURN', 'REVERT'):
                returndata = solve(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')

        # World sanity checks - those should not change, right?
        self.assertEqual(solve(world.block_number()), 0)
        self.assertEqual(solve(world.block_gaslimit()), 1000000)
        self.assertEqual(solve(world.block_timestamp()), 1)
        self.assertEqual(solve(world.block_difficulty()), 256)
        self.assertEqual(solve(world.block_coinbase()), 244687034288125203496486448490407391986876152250)

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 0)
        self.assertEqual(solve(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 100000000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('45600055'))
        # check storage
        self.assertEqual(solve(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0x0f4240)
        # check outs
        self.assertEqual(returndata, unhexlify(''))
        # check logs
        logs = [Log(unhexlify('{:040x}'.format(l.address)), l.topics, solve(l.memlog)) for l in world.logs]
        data = rlp.encode(logs)
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')

        # test used gas
        self.assertEqual(solve(world.current_vm.gas), 79995)

    def test_number(self):
        """
        Textcase taken from https://github.com/ethereum/tests
        File: number.json
        sha256sum: cced67c3cea4a07ce9c4c15107f87a2d6e958cf065791d7c793a260575e9b140
        Code:     NUMBER
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

        blocknumber = 1
        timestamp = 1
        difficulty = 256
        coinbase = 244687034288125203496486448490407391986876152250
        gaslimit = 1000000
        world = evm.EVMWorld(constraints, blocknumber=blocknumber, timestamp=timestamp, difficulty=difficulty,
                             coinbase=coinbase, gaslimit=gaslimit)
    
        acc_addr = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        acc_code = unhexlify('43600055')
        acc_balance = 100000000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        caller = 0xcd1722f3947def4cf144679da39c4c32bdc35681
        price = 0x5af3107a4000
        value = 1000000000000000000
        gas = 100000
        data = ''
        # open a fake tx, no funds send
        world._open_transaction('CALL', address, price, data, caller, value, gas=gas)

        # This variable might seem redundant in some tests - don't forget it is auto generated
        # and there are cases in which we need it ;)
        result = None
        returndata = b''
        try:
            while True:
                world.current_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if result in ('RETURN', 'REVERT'):
                returndata = solve(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')

        # World sanity checks - those should not change, right?
        self.assertEqual(solve(world.block_number()), 1)
        self.assertEqual(solve(world.block_gaslimit()), 1000000)
        self.assertEqual(solve(world.block_timestamp()), 1)
        self.assertEqual(solve(world.block_difficulty()), 256)
        self.assertEqual(solve(world.block_coinbase()), 244687034288125203496486448490407391986876152250)

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 0)
        self.assertEqual(solve(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 100000000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('43600055'))
        # check storage
        self.assertEqual(solve(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0x01)
        # check outs
        self.assertEqual(returndata, unhexlify(''))
        # check logs
        logs = [Log(unhexlify('{:040x}'.format(l.address)), l.topics, solve(l.memlog)) for l in world.logs]
        data = rlp.encode(logs)
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')

        # test used gas
        self.assertEqual(solve(world.current_vm.gas), 79995)

    def test_difficulty(self):
        """
        Textcase taken from https://github.com/ethereum/tests
        File: difficulty.json
        sha256sum: cfb16af60a9bb9474abfff3b66f8f93505c340ab51b4e934fb75806ad87942e5
        Code:     DIFFICULTY
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
        world = evm.EVMWorld(constraints, blocknumber=blocknumber, timestamp=timestamp, difficulty=difficulty,
                             coinbase=coinbase, gaslimit=gaslimit)
    
        acc_addr = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        acc_code = unhexlify('44600055')
        acc_balance = 100000000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        caller = 0xcd1722f3947def4cf144679da39c4c32bdc35681
        price = 0x5af3107a4000
        value = 1000000000000000000
        gas = 100000
        data = ''
        # open a fake tx, no funds send
        world._open_transaction('CALL', address, price, data, caller, value, gas=gas)

        # This variable might seem redundant in some tests - don't forget it is auto generated
        # and there are cases in which we need it ;)
        result = None
        returndata = b''
        try:
            while True:
                world.current_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if result in ('RETURN', 'REVERT'):
                returndata = solve(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')

        # World sanity checks - those should not change, right?
        self.assertEqual(solve(world.block_number()), 0)
        self.assertEqual(solve(world.block_gaslimit()), 1000000)
        self.assertEqual(solve(world.block_timestamp()), 1)
        self.assertEqual(solve(world.block_difficulty()), 256)
        self.assertEqual(solve(world.block_coinbase()), 244687034288125203496486448490407391986876152250)

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 0)
        self.assertEqual(solve(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 100000000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('44600055'))
        # check storage
        self.assertEqual(solve(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0x0100)
        # check outs
        self.assertEqual(returndata, unhexlify(''))
        # check logs
        logs = [Log(unhexlify('{:040x}'.format(l.address)), l.topics, solve(l.memlog)) for l in world.logs]
        data = rlp.encode(logs)
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')

        # test used gas
        self.assertEqual(solve(world.current_vm.gas), 79995)

    def test_coinbase(self):
        """
        Textcase taken from https://github.com/ethereum/tests
        File: coinbase.json
        sha256sum: 112d05c5ec45f9610d75fbd5e95a6bc8b9027c702101c254ee5d667c833e370f
        Code:     COINBASE
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
        world = evm.EVMWorld(constraints, blocknumber=blocknumber, timestamp=timestamp, difficulty=difficulty,
                             coinbase=coinbase, gaslimit=gaslimit)
    
        acc_addr = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        acc_code = unhexlify('41600055')
        acc_balance = 100000000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        caller = 0xcd1722f3947def4cf144679da39c4c32bdc35681
        price = 0x5af3107a4000
        value = 1000000000000000000
        gas = 100000
        data = ''
        # open a fake tx, no funds send
        world._open_transaction('CALL', address, price, data, caller, value, gas=gas)

        # This variable might seem redundant in some tests - don't forget it is auto generated
        # and there are cases in which we need it ;)
        result = None
        returndata = b''
        try:
            while True:
                world.current_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if result in ('RETURN', 'REVERT'):
                returndata = solve(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')

        # World sanity checks - those should not change, right?
        self.assertEqual(solve(world.block_number()), 0)
        self.assertEqual(solve(world.block_gaslimit()), 1000000)
        self.assertEqual(solve(world.block_timestamp()), 1)
        self.assertEqual(solve(world.block_difficulty()), 256)
        self.assertEqual(solve(world.block_coinbase()), 244687034288125203496486448490407391986876152250)

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 0)
        self.assertEqual(solve(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 100000000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('41600055'))
        # check storage
        self.assertEqual(solve(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0x2adc25665018aa1fe0e6bc666dac8fc2697ff9ba)
        # check outs
        self.assertEqual(returndata, unhexlify(''))
        # check logs
        logs = [Log(unhexlify('{:040x}'.format(l.address)), l.topics, solve(l.memlog)) for l in world.logs]
        data = rlp.encode(logs)
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')

        # test used gas
        self.assertEqual(solve(world.current_vm.gas), 79995)

    def test_timestamp(self):
        """
        Textcase taken from https://github.com/ethereum/tests
        File: timestamp.json
        sha256sum: e0517702c3ba8bc8a593af7dbdb4de4d3ee7a53ae4fffc058776e40c435b20ba
        Code:     TIMESTAMP
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
        world = evm.EVMWorld(constraints, blocknumber=blocknumber, timestamp=timestamp, difficulty=difficulty,
                             coinbase=coinbase, gaslimit=gaslimit)
    
        acc_addr = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        acc_code = unhexlify('42600055')
        acc_balance = 100000000000000000000000
        acc_nonce = 0

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        caller = 0xcd1722f3947def4cf144679da39c4c32bdc35681
        price = 0x5af3107a4000
        value = 1000000000000000000
        gas = 100000
        data = ''
        # open a fake tx, no funds send
        world._open_transaction('CALL', address, price, data, caller, value, gas=gas)

        # This variable might seem redundant in some tests - don't forget it is auto generated
        # and there are cases in which we need it ;)
        result = None
        returndata = b''
        try:
            while True:
                world.current_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if result in ('RETURN', 'REVERT'):
                returndata = solve(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')

        # World sanity checks - those should not change, right?
        self.assertEqual(solve(world.block_number()), 0)
        self.assertEqual(solve(world.block_gaslimit()), 1000000)
        self.assertEqual(solve(world.block_timestamp()), 1)
        self.assertEqual(solve(world.block_difficulty()), 256)
        self.assertEqual(solve(world.block_coinbase()), 244687034288125203496486448490407391986876152250)

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 0)
        self.assertEqual(solve(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 100000000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('42600055'))
        # check storage
        self.assertEqual(solve(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0x01)
        # check outs
        self.assertEqual(returndata, unhexlify(''))
        # check logs
        logs = [Log(unhexlify('{:040x}'.format(l.address)), l.topics, solve(l.memlog)) for l in world.logs]
        data = rlp.encode(logs)
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')

        # test used gas
        self.assertEqual(solve(world.current_vm.gas), 79995)


if __name__ == '__main__':
    unittest.main()
