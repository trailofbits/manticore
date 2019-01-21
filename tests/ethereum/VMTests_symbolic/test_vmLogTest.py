"""DO NOT MODIFY: Tests generated from `VMTests/vmLogTest` with make_VMTests.py"""
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


class EVMTest_vmLogTest(unittest.TestCase):
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

    def test_log2_logMemsizeTooHigh(self):
        """
        Textcase taken from https://github.com/ethereum/tests
        File: log2_logMemsizeTooHigh.json
        sha256sum: ad46345861ea0cf01882ff817b9ea1cb7f0c1afc04aba505caa9675714d51748
        Code:     PUSH32 0xaabbffffffffffffffffffffffffffffffffffffffffffffffffffffffffccdd
                  PUSH1 0x0
                  MSTORE
                  PUSH1 0x0
                  PUSH1 0x0
                  PUSH32 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
                  PUSH1 0x1
                  LOG2
        """    
    
        solver = Z3Solver()

        def solve(val):
            results = solver.get_all_values(constraints, val)
            # We constrain all values to single values!
            self.assertEqual(len(results), 1)
            return results[0]

        constraints = ConstraintSet()

        blocknumber = constraints.new_bitvec(256, name='blocknumber')
        constraints.add(blocknumber == 0)

        timestamp = constraints.new_bitvec(256, name='timestamp')
        constraints.add(timestamp == 1)

        difficulty = constraints.new_bitvec(256, name='difficulty')
        constraints.add(difficulty == 256)

        coinbase = constraints.new_bitvec(256, name='coinbase')
        constraints.add(coinbase == 244687034288125203496486448490407391986876152250)

        gaslimit = constraints.new_bitvec(256, name='gaslimit')
        constraints.add(gaslimit == 1000000)

        world = evm.EVMWorld(constraints, blocknumber=blocknumber, timestamp=timestamp, difficulty=difficulty,
                             coinbase=coinbase, gaslimit=gaslimit)
    
        acc_addr = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        acc_code = unhexlify('7faabbffffffffffffffffffffffffffffffffffffffffffffffffffffffffccdd600052600060007fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff6001a2')
            
        acc_balance = constraints.new_bitvec(256, name='balance_0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6')
        constraints.add(acc_balance == 100000000000000000000000)

        acc_nonce = constraints.new_bitvec(256, name='nonce_0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6')
        constraints.add(acc_nonce == 0)

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        caller = 0xcd1722f3947def4cf144679da39c4c32bdc35681
        price = constraints.new_bitvec(256, name='price')
        constraints.add(price == 100000000000000)

        value = constraints.new_bitvec(256, name='value')
        constraints.add(value == 1000000000000000000)

        gas = constraints.new_bitvec(256, name='gas')
        constraints.add(gas == 100000)

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

        # If test end in exception check it here
        self.assertTrue(result == 'THROW')

    def test_log1_nonEmptyMem(self):
        """
        Textcase taken from https://github.com/ethereum/tests
        File: log1_nonEmptyMem.json
        sha256sum: a5460e31fda8616be9b9a32827794dc693cbfda93fbf4933553eea157fbf227d
        Code:     PUSH32 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
                  PUSH1 0x0
                  MSTORE
                  PUSH1 0x0
                  PUSH1 0x20
                  PUSH1 0x0
                  LOG1
        """    
    
        solver = Z3Solver()

        def solve(val):
            results = solver.get_all_values(constraints, val)
            # We constrain all values to single values!
            self.assertEqual(len(results), 1)
            return results[0]

        constraints = ConstraintSet()

        blocknumber = constraints.new_bitvec(256, name='blocknumber')
        constraints.add(blocknumber == 0)

        timestamp = constraints.new_bitvec(256, name='timestamp')
        constraints.add(timestamp == 1)

        difficulty = constraints.new_bitvec(256, name='difficulty')
        constraints.add(difficulty == 256)

        coinbase = constraints.new_bitvec(256, name='coinbase')
        constraints.add(coinbase == 244687034288125203496486448490407391986876152250)

        gaslimit = constraints.new_bitvec(256, name='gaslimit')
        constraints.add(gaslimit == 1000000)

        world = evm.EVMWorld(constraints, blocknumber=blocknumber, timestamp=timestamp, difficulty=difficulty,
                             coinbase=coinbase, gaslimit=gaslimit)
    
        acc_addr = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        acc_code = unhexlify('7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff600052600060206000a1')
            
        acc_balance = constraints.new_bitvec(256, name='balance_0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6')
        constraints.add(acc_balance == 100000000000000000000000)

        acc_nonce = constraints.new_bitvec(256, name='nonce_0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6')
        constraints.add(acc_nonce == 0)

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        caller = 0xcd1722f3947def4cf144679da39c4c32bdc35681
        price = constraints.new_bitvec(256, name='price')
        constraints.add(price == 100000000000000)

        value = constraints.new_bitvec(256, name='value')
        constraints.add(value == 1000000000000000000)

        gas = constraints.new_bitvec(256, name='gas')
        constraints.add(gas == 100000)

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
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff600052600060206000a1'))
        # check outs
        self.assertEqual(returndata, unhexlify(''))
        # check logs
        logs = [Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs]
        data = rlp.encode(logs)
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '2e3c489a64cf3233b1ac4d42fd1f6e2430f6d99524c57dba5471d3b41a20fdc0')

        # test used gas
        self.assertEqual(solve(world.current_vm.gas), 98973)

    def test_log4_logMemsizeZero(self):
        """
        Textcase taken from https://github.com/ethereum/tests
        File: log4_logMemsizeZero.json
        sha256sum: 8df428a3745639c787be050599d9afaf811dd3d5d9b6a7e56b74ce7ffa18865c
        Code:     PUSH32 0xaabbffffffffffffffffffffffffffffffffffffffffffffffffffffffffccdd
                  PUSH1 0x0
                  MSTORE
                  PUSH1 0x0
                  PUSH1 0x0
                  PUSH1 0x0
                  PUSH1 0x0
                  PUSH1 0x0
                  PUSH1 0x1
                  LOG4
        """    
    
        solver = Z3Solver()

        def solve(val):
            results = solver.get_all_values(constraints, val)
            # We constrain all values to single values!
            self.assertEqual(len(results), 1)
            return results[0]

        constraints = ConstraintSet()

        blocknumber = constraints.new_bitvec(256, name='blocknumber')
        constraints.add(blocknumber == 0)

        timestamp = constraints.new_bitvec(256, name='timestamp')
        constraints.add(timestamp == 1)

        difficulty = constraints.new_bitvec(256, name='difficulty')
        constraints.add(difficulty == 256)

        coinbase = constraints.new_bitvec(256, name='coinbase')
        constraints.add(coinbase == 244687034288125203496486448490407391986876152250)

        gaslimit = constraints.new_bitvec(256, name='gaslimit')
        constraints.add(gaslimit == 1000000)

        world = evm.EVMWorld(constraints, blocknumber=blocknumber, timestamp=timestamp, difficulty=difficulty,
                             coinbase=coinbase, gaslimit=gaslimit)
    
        acc_addr = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        acc_code = unhexlify('7faabbffffffffffffffffffffffffffffffffffffffffffffffffffffffffccdd600052600060006000600060006001a4')
            
        acc_balance = constraints.new_bitvec(256, name='balance_0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6')
        constraints.add(acc_balance == 100000000000000000000000)

        acc_nonce = constraints.new_bitvec(256, name='nonce_0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6')
        constraints.add(acc_nonce == 0)

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        caller = 0xcd1722f3947def4cf144679da39c4c32bdc35681
        price = constraints.new_bitvec(256, name='price')
        constraints.add(price == 100000000000000)

        value = constraints.new_bitvec(256, name='value')
        constraints.add(value == 1000000000000000000)

        gas = constraints.new_bitvec(256, name='gas')
        constraints.add(gas == 100000)

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
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('7faabbffffffffffffffffffffffffffffffffffffffffffffffffffffffffccdd600052600060006000600060006001a4'))
        # check outs
        self.assertEqual(returndata, unhexlify(''))
        # check logs
        logs = [Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs]
        data = rlp.encode(logs)
        self.assertEqual(sha3.keccak_256(data).hexdigest(), 'c04befec57a9284dbf7636641a59a938acf437ae400154e34ad0a1cfeee3eaa9')

        # test used gas
        self.assertEqual(solve(world.current_vm.gas), 98095)

    def test_log1_emptyMem(self):
        """
        Textcase taken from https://github.com/ethereum/tests
        File: log1_emptyMem.json
        sha256sum: 92f0894d3a39e8eeba6a8a7637de7fa7a93a51ec2cfdff11beae6414ee7afba7
        Code:     PUSH1 0x0
                  PUSH1 0x0
                  PUSH1 0x0
                  LOG1
        """    
    
        solver = Z3Solver()

        def solve(val):
            results = solver.get_all_values(constraints, val)
            # We constrain all values to single values!
            self.assertEqual(len(results), 1)
            return results[0]

        constraints = ConstraintSet()

        blocknumber = constraints.new_bitvec(256, name='blocknumber')
        constraints.add(blocknumber == 0)

        timestamp = constraints.new_bitvec(256, name='timestamp')
        constraints.add(timestamp == 1)

        difficulty = constraints.new_bitvec(256, name='difficulty')
        constraints.add(difficulty == 256)

        coinbase = constraints.new_bitvec(256, name='coinbase')
        constraints.add(coinbase == 244687034288125203496486448490407391986876152250)

        gaslimit = constraints.new_bitvec(256, name='gaslimit')
        constraints.add(gaslimit == 1000000)

        world = evm.EVMWorld(constraints, blocknumber=blocknumber, timestamp=timestamp, difficulty=difficulty,
                             coinbase=coinbase, gaslimit=gaslimit)
    
        acc_addr = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        acc_code = unhexlify('600060006000a1')
            
        acc_balance = constraints.new_bitvec(256, name='balance_0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6')
        constraints.add(acc_balance == 100000000000000000000000)

        acc_nonce = constraints.new_bitvec(256, name='nonce_0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6')
        constraints.add(acc_nonce == 0)

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        caller = 0xcd1722f3947def4cf144679da39c4c32bdc35681
        price = constraints.new_bitvec(256, name='price')
        constraints.add(price == 100000000000000)

        value = constraints.new_bitvec(256, name='value')
        constraints.add(value == 1000000000000000000)

        gas = constraints.new_bitvec(256, name='gas')
        constraints.add(gas == 100000)

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
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('600060006000a1'))
        # check outs
        self.assertEqual(returndata, unhexlify(''))
        # check logs
        logs = [Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs]
        data = rlp.encode(logs)
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '7a0b07b554f8629b2183374bf734bfd10f641d640654b6f8e5cc088467f90b3d')

        # test used gas
        self.assertEqual(solve(world.current_vm.gas), 99241)

    def test_log0_logMemsizeZero(self):
        """
        Textcase taken from https://github.com/ethereum/tests
        File: log0_logMemsizeZero.json
        sha256sum: c63c403419eb961fc7a058859f6657076848cb6d1c9ea0b915844d046031dfe0
        Code:     PUSH32 0xaabbffffffffffffffffffffffffffffffffffffffffffffffffffffffffccdd
                  PUSH1 0x0
                  MSTORE
                  PUSH1 0x0
                  PUSH1 0x1
                  LOG0
        """    
    
        solver = Z3Solver()

        def solve(val):
            results = solver.get_all_values(constraints, val)
            # We constrain all values to single values!
            self.assertEqual(len(results), 1)
            return results[0]

        constraints = ConstraintSet()

        blocknumber = constraints.new_bitvec(256, name='blocknumber')
        constraints.add(blocknumber == 0)

        timestamp = constraints.new_bitvec(256, name='timestamp')
        constraints.add(timestamp == 1)

        difficulty = constraints.new_bitvec(256, name='difficulty')
        constraints.add(difficulty == 256)

        coinbase = constraints.new_bitvec(256, name='coinbase')
        constraints.add(coinbase == 244687034288125203496486448490407391986876152250)

        gaslimit = constraints.new_bitvec(256, name='gaslimit')
        constraints.add(gaslimit == 1000000)

        world = evm.EVMWorld(constraints, blocknumber=blocknumber, timestamp=timestamp, difficulty=difficulty,
                             coinbase=coinbase, gaslimit=gaslimit)
    
        acc_addr = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        acc_code = unhexlify('7faabbffffffffffffffffffffffffffffffffffffffffffffffffffffffffccdd60005260006001a0')
            
        acc_balance = constraints.new_bitvec(256, name='balance_0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6')
        constraints.add(acc_balance == 100000000000000000000000)

        acc_nonce = constraints.new_bitvec(256, name='nonce_0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6')
        constraints.add(acc_nonce == 0)

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        caller = 0xcd1722f3947def4cf144679da39c4c32bdc35681
        price = constraints.new_bitvec(256, name='price')
        constraints.add(price == 100000000000000)

        value = constraints.new_bitvec(256, name='value')
        constraints.add(value == 1000000000000000000)

        gas = constraints.new_bitvec(256, name='gas')
        constraints.add(gas == 100000)

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
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('7faabbffffffffffffffffffffffffffffffffffffffffffffffffffffffffccdd60005260006001a0'))
        # check outs
        self.assertEqual(returndata, unhexlify(''))
        # check logs
        logs = [Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs]
        data = rlp.encode(logs)
        self.assertEqual(sha3.keccak_256(data).hexdigest(), 'ea63b4dbbdbca1bd985580a0c3b6f35a4955d4d4cf0b4d903003cdfc4c40ba1c')

        # test used gas
        self.assertEqual(solve(world.current_vm.gas), 99607)

    def test_log2_emptyMem(self):
        """
        Textcase taken from https://github.com/ethereum/tests
        File: log2_emptyMem.json
        sha256sum: 3e45405cef7809ad6e49f8e8cdfe0f65264c1338b79da36c13b81f2a7aad8d77
        Code:     PUSH1 0x0
                  PUSH1 0x0
                  PUSH1 0x0
                  PUSH1 0x0
                  LOG2
        """    
    
        solver = Z3Solver()

        def solve(val):
            results = solver.get_all_values(constraints, val)
            # We constrain all values to single values!
            self.assertEqual(len(results), 1)
            return results[0]

        constraints = ConstraintSet()

        blocknumber = constraints.new_bitvec(256, name='blocknumber')
        constraints.add(blocknumber == 0)

        timestamp = constraints.new_bitvec(256, name='timestamp')
        constraints.add(timestamp == 1)

        difficulty = constraints.new_bitvec(256, name='difficulty')
        constraints.add(difficulty == 256)

        coinbase = constraints.new_bitvec(256, name='coinbase')
        constraints.add(coinbase == 244687034288125203496486448490407391986876152250)

        gaslimit = constraints.new_bitvec(256, name='gaslimit')
        constraints.add(gaslimit == 1000000)

        world = evm.EVMWorld(constraints, blocknumber=blocknumber, timestamp=timestamp, difficulty=difficulty,
                             coinbase=coinbase, gaslimit=gaslimit)
    
        acc_addr = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        acc_code = unhexlify('6000600060006000a2')
            
        acc_balance = constraints.new_bitvec(256, name='balance_0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6')
        constraints.add(acc_balance == 100000000000000000000000)

        acc_nonce = constraints.new_bitvec(256, name='nonce_0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6')
        constraints.add(acc_nonce == 0)

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        caller = 0xcd1722f3947def4cf144679da39c4c32bdc35681
        price = constraints.new_bitvec(256, name='price')
        constraints.add(price == 100000000000000)

        value = constraints.new_bitvec(256, name='value')
        constraints.add(value == 1000000000000000000)

        gas = constraints.new_bitvec(256, name='gas')
        constraints.add(gas == 100000)

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
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('6000600060006000a2'))
        # check outs
        self.assertEqual(returndata, unhexlify(''))
        # check logs
        logs = [Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs]
        data = rlp.encode(logs)
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '0c102e52fb694e84eb201c93bc66cb205a9a332215f84188aec1096553289381')

        # test used gas
        self.assertEqual(solve(world.current_vm.gas), 98863)

    def test_log4_nonEmptyMem_logMemSize1_logMemStart31(self):
        """
        Textcase taken from https://github.com/ethereum/tests
        File: log4_nonEmptyMem_logMemSize1_logMemStart31.json
        sha256sum: 88902695664dae25ab70b2e0fbd6ec4a4f0c639b7d16751838500a46241340b4
        Code:     PUSH32 0xaabbffffffffffffffffffffffffffffffffffffffffffffffffffffffffccdd
                  PUSH1 0x0
                  MSTORE
                  PUSH1 0x0
                  PUSH1 0x0
                  PUSH1 0x0
                  PUSH1 0x0
                  PUSH1 0x1
                  PUSH1 0x1f
                  LOG4
        """    
    
        solver = Z3Solver()

        def solve(val):
            results = solver.get_all_values(constraints, val)
            # We constrain all values to single values!
            self.assertEqual(len(results), 1)
            return results[0]

        constraints = ConstraintSet()

        blocknumber = constraints.new_bitvec(256, name='blocknumber')
        constraints.add(blocknumber == 0)

        timestamp = constraints.new_bitvec(256, name='timestamp')
        constraints.add(timestamp == 1)

        difficulty = constraints.new_bitvec(256, name='difficulty')
        constraints.add(difficulty == 256)

        coinbase = constraints.new_bitvec(256, name='coinbase')
        constraints.add(coinbase == 244687034288125203496486448490407391986876152250)

        gaslimit = constraints.new_bitvec(256, name='gaslimit')
        constraints.add(gaslimit == 1000000)

        world = evm.EVMWorld(constraints, blocknumber=blocknumber, timestamp=timestamp, difficulty=difficulty,
                             coinbase=coinbase, gaslimit=gaslimit)
    
        acc_addr = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        acc_code = unhexlify('7faabbffffffffffffffffffffffffffffffffffffffffffffffffffffffffccdd60005260006000600060006001601fa4')
            
        acc_balance = constraints.new_bitvec(256, name='balance_0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6')
        constraints.add(acc_balance == 100000000000000000000000)

        acc_nonce = constraints.new_bitvec(256, name='nonce_0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6')
        constraints.add(acc_nonce == 0)

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        caller = 0xcd1722f3947def4cf144679da39c4c32bdc35681
        price = constraints.new_bitvec(256, name='price')
        constraints.add(price == 100000000000000)

        value = constraints.new_bitvec(256, name='value')
        constraints.add(value == 1000000000000000000)

        gas = constraints.new_bitvec(256, name='gas')
        constraints.add(gas == 100000)

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
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('7faabbffffffffffffffffffffffffffffffffffffffffffffffffffffffffccdd60005260006000600060006001601fa4'))
        # check outs
        self.assertEqual(returndata, unhexlify(''))
        # check logs
        logs = [Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs]
        data = rlp.encode(logs)
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '09928203a19d172f9c404eb76d61e6f4aedc83a2cada1ac2a02ad6aa0e98044b')

        # test used gas
        self.assertEqual(solve(world.current_vm.gas), 98087)

    def test_log1_logMemsizeZero(self):
        """
        Textcase taken from https://github.com/ethereum/tests
        File: log1_logMemsizeZero.json
        sha256sum: 8ad82bc2f38f4a667e3c4ddc19900b0a50d783fe61bbb2e72bb9c5d2bf417d91
        Code:     PUSH32 0xaabbffffffffffffffffffffffffffffffffffffffffffffffffffffffffccdd
                  PUSH1 0x0
                  MSTORE
                  PUSH1 0x0
                  PUSH1 0x0
                  PUSH1 0x1
                  LOG1
        """    
    
        solver = Z3Solver()

        def solve(val):
            results = solver.get_all_values(constraints, val)
            # We constrain all values to single values!
            self.assertEqual(len(results), 1)
            return results[0]

        constraints = ConstraintSet()

        blocknumber = constraints.new_bitvec(256, name='blocknumber')
        constraints.add(blocknumber == 0)

        timestamp = constraints.new_bitvec(256, name='timestamp')
        constraints.add(timestamp == 1)

        difficulty = constraints.new_bitvec(256, name='difficulty')
        constraints.add(difficulty == 256)

        coinbase = constraints.new_bitvec(256, name='coinbase')
        constraints.add(coinbase == 244687034288125203496486448490407391986876152250)

        gaslimit = constraints.new_bitvec(256, name='gaslimit')
        constraints.add(gaslimit == 1000000)

        world = evm.EVMWorld(constraints, blocknumber=blocknumber, timestamp=timestamp, difficulty=difficulty,
                             coinbase=coinbase, gaslimit=gaslimit)
    
        acc_addr = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        acc_code = unhexlify('7faabbffffffffffffffffffffffffffffffffffffffffffffffffffffffffccdd600052600060006001a1')
            
        acc_balance = constraints.new_bitvec(256, name='balance_0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6')
        constraints.add(acc_balance == 100000000000000000000000)

        acc_nonce = constraints.new_bitvec(256, name='nonce_0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6')
        constraints.add(acc_nonce == 0)

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        caller = 0xcd1722f3947def4cf144679da39c4c32bdc35681
        price = constraints.new_bitvec(256, name='price')
        constraints.add(price == 100000000000000)

        value = constraints.new_bitvec(256, name='value')
        constraints.add(value == 1000000000000000000)

        gas = constraints.new_bitvec(256, name='gas')
        constraints.add(gas == 100000)

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
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('7faabbffffffffffffffffffffffffffffffffffffffffffffffffffffffffccdd600052600060006001a1'))
        # check outs
        self.assertEqual(returndata, unhexlify(''))
        # check logs
        logs = [Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs]
        data = rlp.encode(logs)
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '7a0b07b554f8629b2183374bf734bfd10f641d640654b6f8e5cc088467f90b3d')

        # test used gas
        self.assertEqual(solve(world.current_vm.gas), 99229)

    def test_log2_Caller(self):
        """
        Textcase taken from https://github.com/ethereum/tests
        File: log2_Caller.json
        sha256sum: de0bbafbf9a112b4920e6e463d2b2b2ea2f7239763ccb0e6b009f5baaa7f3776
        Code:     PUSH1 0xff
                  PUSH1 0x0
                  MSTORE8
                  CALLER
                  PUSH1 0x0
                  PUSH1 0x20
                  PUSH1 0x0
                  LOG2
        """    
    
        solver = Z3Solver()

        def solve(val):
            results = solver.get_all_values(constraints, val)
            # We constrain all values to single values!
            self.assertEqual(len(results), 1)
            return results[0]

        constraints = ConstraintSet()

        blocknumber = constraints.new_bitvec(256, name='blocknumber')
        constraints.add(blocknumber == 0)

        timestamp = constraints.new_bitvec(256, name='timestamp')
        constraints.add(timestamp == 1)

        difficulty = constraints.new_bitvec(256, name='difficulty')
        constraints.add(difficulty == 256)

        coinbase = constraints.new_bitvec(256, name='coinbase')
        constraints.add(coinbase == 244687034288125203496486448490407391986876152250)

        gaslimit = constraints.new_bitvec(256, name='gaslimit')
        constraints.add(gaslimit == 1000000)

        world = evm.EVMWorld(constraints, blocknumber=blocknumber, timestamp=timestamp, difficulty=difficulty,
                             coinbase=coinbase, gaslimit=gaslimit)
    
        acc_addr = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        acc_code = unhexlify('60ff60005333600060206000a2')
            
        acc_balance = constraints.new_bitvec(256, name='balance_0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6')
        constraints.add(acc_balance == 100000000000000000000000)

        acc_nonce = constraints.new_bitvec(256, name='nonce_0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6')
        constraints.add(acc_nonce == 0)

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        caller = 0xcd1722f3947def4cf144679da39c4c32bdc35681
        price = constraints.new_bitvec(256, name='price')
        constraints.add(price == 100000000000000)

        value = constraints.new_bitvec(256, name='value')
        constraints.add(value == 1000000000000000000)

        gas = constraints.new_bitvec(256, name='gas')
        constraints.add(gas == 100000)

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
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('60ff60005333600060206000a2'))
        # check outs
        self.assertEqual(returndata, unhexlify(''))
        # check logs
        logs = [Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs]
        data = rlp.encode(logs)
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '142b142cb8656b9fdb44d0a126ba5165dbe681511a76f7ba1d0cb9c7b6a56790')

        # test used gas
        self.assertEqual(solve(world.current_vm.gas), 98596)

    def test_log1_logMemsizeTooHigh(self):
        """
        Textcase taken from https://github.com/ethereum/tests
        File: log1_logMemsizeTooHigh.json
        sha256sum: 578ab3931d616c8eb81045cc271b571f17cb9f596f27709132430438ff969372
        Code:     PUSH32 0xaabbffffffffffffffffffffffffffffffffffffffffffffffffffffffffccdd
                  PUSH1 0x0
                  MSTORE
                  PUSH1 0x0
                  PUSH32 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
                  PUSH1 0x1
                  LOG1
        """    
    
        solver = Z3Solver()

        def solve(val):
            results = solver.get_all_values(constraints, val)
            # We constrain all values to single values!
            self.assertEqual(len(results), 1)
            return results[0]

        constraints = ConstraintSet()

        blocknumber = constraints.new_bitvec(256, name='blocknumber')
        constraints.add(blocknumber == 0)

        timestamp = constraints.new_bitvec(256, name='timestamp')
        constraints.add(timestamp == 1)

        difficulty = constraints.new_bitvec(256, name='difficulty')
        constraints.add(difficulty == 256)

        coinbase = constraints.new_bitvec(256, name='coinbase')
        constraints.add(coinbase == 244687034288125203496486448490407391986876152250)

        gaslimit = constraints.new_bitvec(256, name='gaslimit')
        constraints.add(gaslimit == 1000000)

        world = evm.EVMWorld(constraints, blocknumber=blocknumber, timestamp=timestamp, difficulty=difficulty,
                             coinbase=coinbase, gaslimit=gaslimit)
    
        acc_addr = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        acc_code = unhexlify('7faabbffffffffffffffffffffffffffffffffffffffffffffffffffffffffccdd60005260007fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff6001a1')
            
        acc_balance = constraints.new_bitvec(256, name='balance_0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6')
        constraints.add(acc_balance == 100000000000000000000000)

        acc_nonce = constraints.new_bitvec(256, name='nonce_0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6')
        constraints.add(acc_nonce == 0)

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        caller = 0xcd1722f3947def4cf144679da39c4c32bdc35681
        price = constraints.new_bitvec(256, name='price')
        constraints.add(price == 100000000000000)

        value = constraints.new_bitvec(256, name='value')
        constraints.add(value == 1000000000000000000)

        gas = constraints.new_bitvec(256, name='gas')
        constraints.add(gas == 100000)

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

        # If test end in exception check it here
        self.assertTrue(result == 'THROW')

    def test_log2_logMemsizeZero(self):
        """
        Textcase taken from https://github.com/ethereum/tests
        File: log2_logMemsizeZero.json
        sha256sum: 183acbc7b246b9c4356123a9e02e9c95875bb3f04b2c182fd715ed9d148f8865
        Code:     PUSH32 0xaabbffffffffffffffffffffffffffffffffffffffffffffffffffffffffccdd
                  PUSH1 0x0
                  MSTORE
                  PUSH1 0x0
                  PUSH1 0x0
                  PUSH1 0x0
                  PUSH1 0x1
                  LOG2
        """    
    
        solver = Z3Solver()

        def solve(val):
            results = solver.get_all_values(constraints, val)
            # We constrain all values to single values!
            self.assertEqual(len(results), 1)
            return results[0]

        constraints = ConstraintSet()

        blocknumber = constraints.new_bitvec(256, name='blocknumber')
        constraints.add(blocknumber == 0)

        timestamp = constraints.new_bitvec(256, name='timestamp')
        constraints.add(timestamp == 1)

        difficulty = constraints.new_bitvec(256, name='difficulty')
        constraints.add(difficulty == 256)

        coinbase = constraints.new_bitvec(256, name='coinbase')
        constraints.add(coinbase == 244687034288125203496486448490407391986876152250)

        gaslimit = constraints.new_bitvec(256, name='gaslimit')
        constraints.add(gaslimit == 1000000)

        world = evm.EVMWorld(constraints, blocknumber=blocknumber, timestamp=timestamp, difficulty=difficulty,
                             coinbase=coinbase, gaslimit=gaslimit)
    
        acc_addr = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        acc_code = unhexlify('7faabbffffffffffffffffffffffffffffffffffffffffffffffffffffffffccdd6000526000600060006001a2')
            
        acc_balance = constraints.new_bitvec(256, name='balance_0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6')
        constraints.add(acc_balance == 100000000000000000000000)

        acc_nonce = constraints.new_bitvec(256, name='nonce_0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6')
        constraints.add(acc_nonce == 0)

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        caller = 0xcd1722f3947def4cf144679da39c4c32bdc35681
        price = constraints.new_bitvec(256, name='price')
        constraints.add(price == 100000000000000)

        value = constraints.new_bitvec(256, name='value')
        constraints.add(value == 1000000000000000000)

        gas = constraints.new_bitvec(256, name='gas')
        constraints.add(gas == 100000)

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
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('7faabbffffffffffffffffffffffffffffffffffffffffffffffffffffffffccdd6000526000600060006001a2'))
        # check outs
        self.assertEqual(returndata, unhexlify(''))
        # check logs
        logs = [Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs]
        data = rlp.encode(logs)
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '0c102e52fb694e84eb201c93bc66cb205a9a332215f84188aec1096553289381')

        # test used gas
        self.assertEqual(solve(world.current_vm.gas), 98851)

    def test_log2_logMemStartTooHigh(self):
        """
        Textcase taken from https://github.com/ethereum/tests
        File: log2_logMemStartTooHigh.json
        sha256sum: 4f21542eb18c50ca13797e4d87c91138cf655bfe4c534613eab3aaa06e1bbe16
        Code:     PUSH32 0xaabbffffffffffffffffffffffffffffffffffffffffffffffffffffffffccdd
                  PUSH1 0x0
                  MSTORE
                  PUSH1 0x0
                  PUSH1 0x0
                  PUSH1 0x1
                  PUSH32 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
                  LOG2
        """    
    
        solver = Z3Solver()

        def solve(val):
            results = solver.get_all_values(constraints, val)
            # We constrain all values to single values!
            self.assertEqual(len(results), 1)
            return results[0]

        constraints = ConstraintSet()

        blocknumber = constraints.new_bitvec(256, name='blocknumber')
        constraints.add(blocknumber == 0)

        timestamp = constraints.new_bitvec(256, name='timestamp')
        constraints.add(timestamp == 1)

        difficulty = constraints.new_bitvec(256, name='difficulty')
        constraints.add(difficulty == 256)

        coinbase = constraints.new_bitvec(256, name='coinbase')
        constraints.add(coinbase == 244687034288125203496486448490407391986876152250)

        gaslimit = constraints.new_bitvec(256, name='gaslimit')
        constraints.add(gaslimit == 1000000)

        world = evm.EVMWorld(constraints, blocknumber=blocknumber, timestamp=timestamp, difficulty=difficulty,
                             coinbase=coinbase, gaslimit=gaslimit)
    
        acc_addr = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        acc_code = unhexlify('7faabbffffffffffffffffffffffffffffffffffffffffffffffffffffffffccdd6000526000600060017fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffa2')
            
        acc_balance = constraints.new_bitvec(256, name='balance_0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6')
        constraints.add(acc_balance == 100000000000000000000000)

        acc_nonce = constraints.new_bitvec(256, name='nonce_0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6')
        constraints.add(acc_nonce == 0)

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        caller = 0xcd1722f3947def4cf144679da39c4c32bdc35681
        price = constraints.new_bitvec(256, name='price')
        constraints.add(price == 100000000000000)

        value = constraints.new_bitvec(256, name='value')
        constraints.add(value == 1000000000000000000)

        gas = constraints.new_bitvec(256, name='gas')
        constraints.add(gas == 100000)

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

        # If test end in exception check it here
        self.assertTrue(result == 'THROW')

    def test_log3_logMemsizeZero(self):
        """
        Textcase taken from https://github.com/ethereum/tests
        File: log3_logMemsizeZero.json
        sha256sum: 5aca11a1da828bb0d55e076c829be9220a5580e6cbe54767d1360e23b3c66702
        Code:     PUSH32 0xaabbffffffffffffffffffffffffffffffffffffffffffffffffffffffffccdd
                  PUSH1 0x0
                  MSTORE
                  PUSH1 0x0
                  PUSH1 0x0
                  PUSH1 0x0
                  PUSH1 0x0
                  PUSH1 0x1
                  LOG3
        """    
    
        solver = Z3Solver()

        def solve(val):
            results = solver.get_all_values(constraints, val)
            # We constrain all values to single values!
            self.assertEqual(len(results), 1)
            return results[0]

        constraints = ConstraintSet()

        blocknumber = constraints.new_bitvec(256, name='blocknumber')
        constraints.add(blocknumber == 0)

        timestamp = constraints.new_bitvec(256, name='timestamp')
        constraints.add(timestamp == 1)

        difficulty = constraints.new_bitvec(256, name='difficulty')
        constraints.add(difficulty == 256)

        coinbase = constraints.new_bitvec(256, name='coinbase')
        constraints.add(coinbase == 244687034288125203496486448490407391986876152250)

        gaslimit = constraints.new_bitvec(256, name='gaslimit')
        constraints.add(gaslimit == 1000000)

        world = evm.EVMWorld(constraints, blocknumber=blocknumber, timestamp=timestamp, difficulty=difficulty,
                             coinbase=coinbase, gaslimit=gaslimit)
    
        acc_addr = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        acc_code = unhexlify('7faabbffffffffffffffffffffffffffffffffffffffffffffffffffffffffccdd60005260006000600060006001a3')
            
        acc_balance = constraints.new_bitvec(256, name='balance_0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6')
        constraints.add(acc_balance == 100000000000000000000000)

        acc_nonce = constraints.new_bitvec(256, name='nonce_0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6')
        constraints.add(acc_nonce == 0)

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        caller = 0xcd1722f3947def4cf144679da39c4c32bdc35681
        price = constraints.new_bitvec(256, name='price')
        constraints.add(price == 100000000000000)

        value = constraints.new_bitvec(256, name='value')
        constraints.add(value == 1000000000000000000)

        gas = constraints.new_bitvec(256, name='gas')
        constraints.add(gas == 100000)

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
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('7faabbffffffffffffffffffffffffffffffffffffffffffffffffffffffffccdd60005260006000600060006001a3'))
        # check outs
        self.assertEqual(returndata, unhexlify(''))
        # check logs
        logs = [Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs]
        data = rlp.encode(logs)
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '79f83975e7ea5efeeb8e2b08ea11bd9f320f34042ce7f2abd4df8a26b04839c0')

        # test used gas
        self.assertEqual(solve(world.current_vm.gas), 98473)

    def test_log2_MaxTopic(self):
        """
        Textcase taken from https://github.com/ethereum/tests
        File: log2_MaxTopic.json
        sha256sum: c858a70982e4354306bde6cec6981f4fd8a717ac3151bbe4b3f9802362fe903e
        Code:     PUSH32 0xaabbffffffffffffffffffffffffffffffffffffffffffffffffffffffffccdd
                  PUSH1 0x0
                  MSTORE
                  PUSH32 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
                  PUSH32 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
                  PUSH1 0x20
                  PUSH1 0x0
                  LOG2
        """    
    
        solver = Z3Solver()

        def solve(val):
            results = solver.get_all_values(constraints, val)
            # We constrain all values to single values!
            self.assertEqual(len(results), 1)
            return results[0]

        constraints = ConstraintSet()

        blocknumber = constraints.new_bitvec(256, name='blocknumber')
        constraints.add(blocknumber == 0)

        timestamp = constraints.new_bitvec(256, name='timestamp')
        constraints.add(timestamp == 1)

        difficulty = constraints.new_bitvec(256, name='difficulty')
        constraints.add(difficulty == 256)

        coinbase = constraints.new_bitvec(256, name='coinbase')
        constraints.add(coinbase == 244687034288125203496486448490407391986876152250)

        gaslimit = constraints.new_bitvec(256, name='gaslimit')
        constraints.add(gaslimit == 1000000)

        world = evm.EVMWorld(constraints, blocknumber=blocknumber, timestamp=timestamp, difficulty=difficulty,
                             coinbase=coinbase, gaslimit=gaslimit)
    
        acc_addr = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        acc_code = unhexlify('7faabbffffffffffffffffffffffffffffffffffffffffffffffffffffffffccdd6000527fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff60206000a2')
            
        acc_balance = constraints.new_bitvec(256, name='balance_0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6')
        constraints.add(acc_balance == 100000000000000000000000)

        acc_nonce = constraints.new_bitvec(256, name='nonce_0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6')
        constraints.add(acc_nonce == 0)

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        caller = 0xcd1722f3947def4cf144679da39c4c32bdc35681
        price = constraints.new_bitvec(256, name='price')
        constraints.add(price == 100000000000000)

        value = constraints.new_bitvec(256, name='value')
        constraints.add(value == 1000000000000000000)

        gas = constraints.new_bitvec(256, name='gas')
        constraints.add(gas == 100000)

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
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('7faabbffffffffffffffffffffffffffffffffffffffffffffffffffffffffccdd6000527fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff60206000a2'))
        # check outs
        self.assertEqual(returndata, unhexlify(''))
        # check logs
        logs = [Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs]
        data = rlp.encode(logs)
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '10038c0bc70265c0308f2914a65cdc63b8e6edfd44850dbe42a05c868edc30f1')

        # test used gas
        self.assertEqual(solve(world.current_vm.gas), 98595)

    def test_log1_logMemStartTooHigh(self):
        """
        Textcase taken from https://github.com/ethereum/tests
        File: log1_logMemStartTooHigh.json
        sha256sum: 51781870be33fb0c8521f539806cf9bbcdc943610afc9bdb6f0cfe6cfffa64af
        Code:     PUSH32 0xaabbffffffffffffffffffffffffffffffffffffffffffffffffffffffffccdd
                  PUSH1 0x0
                  MSTORE
                  PUSH1 0x0
                  PUSH1 0x1
                  PUSH32 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
                  LOG1
        """    
    
        solver = Z3Solver()

        def solve(val):
            results = solver.get_all_values(constraints, val)
            # We constrain all values to single values!
            self.assertEqual(len(results), 1)
            return results[0]

        constraints = ConstraintSet()

        blocknumber = constraints.new_bitvec(256, name='blocknumber')
        constraints.add(blocknumber == 0)

        timestamp = constraints.new_bitvec(256, name='timestamp')
        constraints.add(timestamp == 1)

        difficulty = constraints.new_bitvec(256, name='difficulty')
        constraints.add(difficulty == 256)

        coinbase = constraints.new_bitvec(256, name='coinbase')
        constraints.add(coinbase == 244687034288125203496486448490407391986876152250)

        gaslimit = constraints.new_bitvec(256, name='gaslimit')
        constraints.add(gaslimit == 1000000)

        world = evm.EVMWorld(constraints, blocknumber=blocknumber, timestamp=timestamp, difficulty=difficulty,
                             coinbase=coinbase, gaslimit=gaslimit)
    
        acc_addr = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        acc_code = unhexlify('7faabbffffffffffffffffffffffffffffffffffffffffffffffffffffffffccdd600052600060017fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffa1')
            
        acc_balance = constraints.new_bitvec(256, name='balance_0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6')
        constraints.add(acc_balance == 100000000000000000000000)

        acc_nonce = constraints.new_bitvec(256, name='nonce_0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6')
        constraints.add(acc_nonce == 0)

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        caller = 0xcd1722f3947def4cf144679da39c4c32bdc35681
        price = constraints.new_bitvec(256, name='price')
        constraints.add(price == 100000000000000)

        value = constraints.new_bitvec(256, name='value')
        constraints.add(value == 1000000000000000000)

        gas = constraints.new_bitvec(256, name='gas')
        constraints.add(gas == 100000)

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

        # If test end in exception check it here
        self.assertTrue(result == 'THROW')

    def test_log0_nonEmptyMem(self):
        """
        Textcase taken from https://github.com/ethereum/tests
        File: log0_nonEmptyMem.json
        sha256sum: 2f8eb6295a2a1c7b184300c911f364eb5b3e9e8bd11f9637d2b97ebc6b0a5b02
        Code:     PUSH32 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
                  PUSH1 0x0
                  MSTORE
                  PUSH1 0x20
                  PUSH1 0x0
                  LOG0
        """    
    
        solver = Z3Solver()

        def solve(val):
            results = solver.get_all_values(constraints, val)
            # We constrain all values to single values!
            self.assertEqual(len(results), 1)
            return results[0]

        constraints = ConstraintSet()

        blocknumber = constraints.new_bitvec(256, name='blocknumber')
        constraints.add(blocknumber == 0)

        timestamp = constraints.new_bitvec(256, name='timestamp')
        constraints.add(timestamp == 1)

        difficulty = constraints.new_bitvec(256, name='difficulty')
        constraints.add(difficulty == 256)

        coinbase = constraints.new_bitvec(256, name='coinbase')
        constraints.add(coinbase == 244687034288125203496486448490407391986876152250)

        gaslimit = constraints.new_bitvec(256, name='gaslimit')
        constraints.add(gaslimit == 1000000)

        world = evm.EVMWorld(constraints, blocknumber=blocknumber, timestamp=timestamp, difficulty=difficulty,
                             coinbase=coinbase, gaslimit=gaslimit)
    
        acc_addr = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        acc_code = unhexlify('7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff60005260206000a0')
            
        acc_balance = constraints.new_bitvec(256, name='balance_0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6')
        constraints.add(acc_balance == 100000000000000000000000)

        acc_nonce = constraints.new_bitvec(256, name='nonce_0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6')
        constraints.add(acc_nonce == 0)

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        caller = 0xcd1722f3947def4cf144679da39c4c32bdc35681
        price = constraints.new_bitvec(256, name='price')
        constraints.add(price == 100000000000000)

        value = constraints.new_bitvec(256, name='value')
        constraints.add(value == 1000000000000000000)

        gas = constraints.new_bitvec(256, name='gas')
        constraints.add(gas == 100000)

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
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff60005260206000a0'))
        # check outs
        self.assertEqual(returndata, unhexlify(''))
        # check logs
        logs = [Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs]
        data = rlp.encode(logs)
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '4b78f5979516c0624506af0eb4124e0a6ae9e21c82a3a90ca2999983634d7338')

        # test used gas
        self.assertEqual(solve(world.current_vm.gas), 99351)

    def test_log0_logMemsizeTooHigh(self):
        """
        Textcase taken from https://github.com/ethereum/tests
        File: log0_logMemsizeTooHigh.json
        sha256sum: d28ac55519085fa97df67e497eb258e1bd832ecc1502167f453194ca9be9cad4
        Code:     PUSH32 0xaabbffffffffffffffffffffffffffffffffffffffffffffffffffffffffccdd
                  PUSH1 0x0
                  MSTORE
                  PUSH32 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
                  PUSH1 0x1
                  LOG0
        """    
    
        solver = Z3Solver()

        def solve(val):
            results = solver.get_all_values(constraints, val)
            # We constrain all values to single values!
            self.assertEqual(len(results), 1)
            return results[0]

        constraints = ConstraintSet()

        blocknumber = constraints.new_bitvec(256, name='blocknumber')
        constraints.add(blocknumber == 0)

        timestamp = constraints.new_bitvec(256, name='timestamp')
        constraints.add(timestamp == 1)

        difficulty = constraints.new_bitvec(256, name='difficulty')
        constraints.add(difficulty == 256)

        coinbase = constraints.new_bitvec(256, name='coinbase')
        constraints.add(coinbase == 244687034288125203496486448490407391986876152250)

        gaslimit = constraints.new_bitvec(256, name='gaslimit')
        constraints.add(gaslimit == 1000000)

        world = evm.EVMWorld(constraints, blocknumber=blocknumber, timestamp=timestamp, difficulty=difficulty,
                             coinbase=coinbase, gaslimit=gaslimit)
    
        acc_addr = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        acc_code = unhexlify('7faabbffffffffffffffffffffffffffffffffffffffffffffffffffffffffccdd6000527fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff6001a0')
            
        acc_balance = constraints.new_bitvec(256, name='balance_0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6')
        constraints.add(acc_balance == 100000000000000000000000)

        acc_nonce = constraints.new_bitvec(256, name='nonce_0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6')
        constraints.add(acc_nonce == 0)

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        caller = 0xcd1722f3947def4cf144679da39c4c32bdc35681
        price = constraints.new_bitvec(256, name='price')
        constraints.add(price == 100000000000000)

        value = constraints.new_bitvec(256, name='value')
        constraints.add(value == 1000000000000000000)

        gas = constraints.new_bitvec(256, name='gas')
        constraints.add(gas == 100000)

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

        # If test end in exception check it here
        self.assertTrue(result == 'THROW')

    def test_log_2logs(self):
        """
        Textcase taken from https://github.com/ethereum/tests
        File: log_2logs.json
        sha256sum: cfcb61671028b46e606f72e79428acf4102fb57177f67112b37879b6e9c8f715
        Code:     PUSH32 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
                  PUSH1 0x0
                  MSTORE
                  PUSH1 0x20
                  PUSH1 0x0
                  LOG0
                  PUSH1 0x10
                  PUSH1 0x2
                  LOG0
        """    
    
        solver = Z3Solver()

        def solve(val):
            results = solver.get_all_values(constraints, val)
            # We constrain all values to single values!
            self.assertEqual(len(results), 1)
            return results[0]

        constraints = ConstraintSet()

        blocknumber = constraints.new_bitvec(256, name='blocknumber')
        constraints.add(blocknumber == 0)

        timestamp = constraints.new_bitvec(256, name='timestamp')
        constraints.add(timestamp == 1)

        difficulty = constraints.new_bitvec(256, name='difficulty')
        constraints.add(difficulty == 256)

        coinbase = constraints.new_bitvec(256, name='coinbase')
        constraints.add(coinbase == 244687034288125203496486448490407391986876152250)

        gaslimit = constraints.new_bitvec(256, name='gaslimit')
        constraints.add(gaslimit == 1000000)

        world = evm.EVMWorld(constraints, blocknumber=blocknumber, timestamp=timestamp, difficulty=difficulty,
                             coinbase=coinbase, gaslimit=gaslimit)
    
        acc_addr = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        acc_code = unhexlify('7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff60005260206000a060106002a0')
            
        acc_balance = constraints.new_bitvec(256, name='balance_0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6')
        constraints.add(acc_balance == 100000000000000000000000)

        acc_nonce = constraints.new_bitvec(256, name='nonce_0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6')
        constraints.add(acc_nonce == 0)

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        caller = 0xcd1722f3947def4cf144679da39c4c32bdc35681
        price = constraints.new_bitvec(256, name='price')
        constraints.add(price == 100000000000000)

        value = constraints.new_bitvec(256, name='value')
        constraints.add(value == 1000000000000000000)

        gas = constraints.new_bitvec(256, name='gas')
        constraints.add(gas == 100000)

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
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff60005260206000a060106002a0'))
        # check outs
        self.assertEqual(returndata, unhexlify(''))
        # check logs
        logs = [Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs]
        data = rlp.encode(logs)
        self.assertEqual(sha3.keccak_256(data).hexdigest(), 'e12ee27cac9d3a99fe2fae82f6a97af4252ea255452ec3724bbec0c8e5d03365')

        # test used gas
        self.assertEqual(solve(world.current_vm.gas), 98842)

    def test_log1_Caller(self):
        """
        Textcase taken from https://github.com/ethereum/tests
        File: log1_Caller.json
        sha256sum: 9315ab755de0d3a82e12960a9f8a2b81bf116eca5e8320bb9f321d9ebdf75484
        Code:     PUSH1 0xff
                  PUSH1 0x0
                  MSTORE8
                  CALLER
                  PUSH1 0x20
                  PUSH1 0x0
                  LOG1
        """    
    
        solver = Z3Solver()

        def solve(val):
            results = solver.get_all_values(constraints, val)
            # We constrain all values to single values!
            self.assertEqual(len(results), 1)
            return results[0]

        constraints = ConstraintSet()

        blocknumber = constraints.new_bitvec(256, name='blocknumber')
        constraints.add(blocknumber == 0)

        timestamp = constraints.new_bitvec(256, name='timestamp')
        constraints.add(timestamp == 1)

        difficulty = constraints.new_bitvec(256, name='difficulty')
        constraints.add(difficulty == 256)

        coinbase = constraints.new_bitvec(256, name='coinbase')
        constraints.add(coinbase == 244687034288125203496486448490407391986876152250)

        gaslimit = constraints.new_bitvec(256, name='gaslimit')
        constraints.add(gaslimit == 1000000)

        world = evm.EVMWorld(constraints, blocknumber=blocknumber, timestamp=timestamp, difficulty=difficulty,
                             coinbase=coinbase, gaslimit=gaslimit)
    
        acc_addr = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        acc_code = unhexlify('60ff6000533360206000a1')
            
        acc_balance = constraints.new_bitvec(256, name='balance_0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6')
        constraints.add(acc_balance == 100000000000000000000000)

        acc_nonce = constraints.new_bitvec(256, name='nonce_0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6')
        constraints.add(acc_nonce == 0)

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        caller = 0xcd1722f3947def4cf144679da39c4c32bdc35681
        price = constraints.new_bitvec(256, name='price')
        constraints.add(price == 100000000000000)

        value = constraints.new_bitvec(256, name='value')
        constraints.add(value == 1000000000000000000)

        gas = constraints.new_bitvec(256, name='gas')
        constraints.add(gas == 100000)

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
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('60ff6000533360206000a1'))
        # check outs
        self.assertEqual(returndata, unhexlify(''))
        # check logs
        logs = [Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs]
        data = rlp.encode(logs)
        self.assertEqual(sha3.keccak_256(data).hexdigest(), 'dcdb7c361ccebf35b55b9853f713765acc075a172ab9077d9cbbfe4e79e1f628')

        # test used gas
        self.assertEqual(solve(world.current_vm.gas), 98974)

    def test_log3_nonEmptyMem_logMemSize1(self):
        """
        Textcase taken from https://github.com/ethereum/tests
        File: log3_nonEmptyMem_logMemSize1.json
        sha256sum: d31aadd67e57e20b2b15e02b6c5bfa92d669df36266c311daabde135868dfc9a
        Code:     PUSH32 0xaabbffffffffffffffffffffffffffffffffffffffffffffffffffffffffccdd
                  PUSH1 0x0
                  MSTORE
                  PUSH1 0x0
                  PUSH1 0x0
                  PUSH1 0x0
                  PUSH1 0x1
                  PUSH1 0x0
                  LOG3
        """    
    
        solver = Z3Solver()

        def solve(val):
            results = solver.get_all_values(constraints, val)
            # We constrain all values to single values!
            self.assertEqual(len(results), 1)
            return results[0]

        constraints = ConstraintSet()

        blocknumber = constraints.new_bitvec(256, name='blocknumber')
        constraints.add(blocknumber == 0)

        timestamp = constraints.new_bitvec(256, name='timestamp')
        constraints.add(timestamp == 1)

        difficulty = constraints.new_bitvec(256, name='difficulty')
        constraints.add(difficulty == 256)

        coinbase = constraints.new_bitvec(256, name='coinbase')
        constraints.add(coinbase == 244687034288125203496486448490407391986876152250)

        gaslimit = constraints.new_bitvec(256, name='gaslimit')
        constraints.add(gaslimit == 1000000)

        world = evm.EVMWorld(constraints, blocknumber=blocknumber, timestamp=timestamp, difficulty=difficulty,
                             coinbase=coinbase, gaslimit=gaslimit)
    
        acc_addr = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        acc_code = unhexlify('7faabbffffffffffffffffffffffffffffffffffffffffffffffffffffffffccdd60005260006000600060016000a3')
            
        acc_balance = constraints.new_bitvec(256, name='balance_0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6')
        constraints.add(acc_balance == 100000000000000000000000)

        acc_nonce = constraints.new_bitvec(256, name='nonce_0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6')
        constraints.add(acc_nonce == 0)

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        caller = 0xcd1722f3947def4cf144679da39c4c32bdc35681
        price = constraints.new_bitvec(256, name='price')
        constraints.add(price == 100000000000000)

        value = constraints.new_bitvec(256, name='value')
        constraints.add(value == 1000000000000000000)

        gas = constraints.new_bitvec(256, name='gas')
        constraints.add(gas == 100000)

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
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('7faabbffffffffffffffffffffffffffffffffffffffffffffffffffffffffccdd60005260006000600060016000a3'))
        # check outs
        self.assertEqual(returndata, unhexlify(''))
        # check logs
        logs = [Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs]
        data = rlp.encode(logs)
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '47b80b4fa66c744dbeef8ec51e7d202f3c03b893dfdc95e3523c223a55ab3051')

        # test used gas
        self.assertEqual(solve(world.current_vm.gas), 98465)

    def test_log0_nonEmptyMem_logMemSize1(self):
        """
        Textcase taken from https://github.com/ethereum/tests
        File: log0_nonEmptyMem_logMemSize1.json
        sha256sum: 8a75f30cf6efb627a7c95d64dc17ac65bb3fdd41d0301faf5bd9914adbd7cc4a
        Code:     PUSH32 0xaabbffffffffffffffffffffffffffffffffffffffffffffffffffffffffccdd
                  PUSH1 0x0
                  MSTORE
                  PUSH1 0x1
                  PUSH1 0x0
                  LOG0
        """    
    
        solver = Z3Solver()

        def solve(val):
            results = solver.get_all_values(constraints, val)
            # We constrain all values to single values!
            self.assertEqual(len(results), 1)
            return results[0]

        constraints = ConstraintSet()

        blocknumber = constraints.new_bitvec(256, name='blocknumber')
        constraints.add(blocknumber == 0)

        timestamp = constraints.new_bitvec(256, name='timestamp')
        constraints.add(timestamp == 1)

        difficulty = constraints.new_bitvec(256, name='difficulty')
        constraints.add(difficulty == 256)

        coinbase = constraints.new_bitvec(256, name='coinbase')
        constraints.add(coinbase == 244687034288125203496486448490407391986876152250)

        gaslimit = constraints.new_bitvec(256, name='gaslimit')
        constraints.add(gaslimit == 1000000)

        world = evm.EVMWorld(constraints, blocknumber=blocknumber, timestamp=timestamp, difficulty=difficulty,
                             coinbase=coinbase, gaslimit=gaslimit)
    
        acc_addr = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        acc_code = unhexlify('7faabbffffffffffffffffffffffffffffffffffffffffffffffffffffffffccdd60005260016000a0')
            
        acc_balance = constraints.new_bitvec(256, name='balance_0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6')
        constraints.add(acc_balance == 100000000000000000000000)

        acc_nonce = constraints.new_bitvec(256, name='nonce_0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6')
        constraints.add(acc_nonce == 0)

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        caller = 0xcd1722f3947def4cf144679da39c4c32bdc35681
        price = constraints.new_bitvec(256, name='price')
        constraints.add(price == 100000000000000)

        value = constraints.new_bitvec(256, name='value')
        constraints.add(value == 1000000000000000000)

        gas = constraints.new_bitvec(256, name='gas')
        constraints.add(gas == 100000)

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
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('7faabbffffffffffffffffffffffffffffffffffffffffffffffffffffffffccdd60005260016000a0'))
        # check outs
        self.assertEqual(returndata, unhexlify(''))
        # check logs
        logs = [Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs]
        data = rlp.encode(logs)
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '20238193c29688c64e395ae6044273a99e54e9cfaec2033f1cdc8967e0409cc1')

        # test used gas
        self.assertEqual(solve(world.current_vm.gas), 99599)

    def test_log4_Caller(self):
        """
        Textcase taken from https://github.com/ethereum/tests
        File: log4_Caller.json
        sha256sum: 9d8adbfeac6cdb354512917e33b9e3a04aa33f06e5422199108042a6232186a2
        Code:     PUSH1 0xff
                  PUSH1 0x0
                  MSTORE8
                  CALLER
                  PUSH1 0x0
                  PUSH1 0x0
                  PUSH1 0x0
                  PUSH1 0x20
                  PUSH1 0x0
                  LOG4
        """    
    
        solver = Z3Solver()

        def solve(val):
            results = solver.get_all_values(constraints, val)
            # We constrain all values to single values!
            self.assertEqual(len(results), 1)
            return results[0]

        constraints = ConstraintSet()

        blocknumber = constraints.new_bitvec(256, name='blocknumber')
        constraints.add(blocknumber == 0)

        timestamp = constraints.new_bitvec(256, name='timestamp')
        constraints.add(timestamp == 1)

        difficulty = constraints.new_bitvec(256, name='difficulty')
        constraints.add(difficulty == 256)

        coinbase = constraints.new_bitvec(256, name='coinbase')
        constraints.add(coinbase == 244687034288125203496486448490407391986876152250)

        gaslimit = constraints.new_bitvec(256, name='gaslimit')
        constraints.add(gaslimit == 1000000)

        world = evm.EVMWorld(constraints, blocknumber=blocknumber, timestamp=timestamp, difficulty=difficulty,
                             coinbase=coinbase, gaslimit=gaslimit)
    
        acc_addr = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        acc_code = unhexlify('60ff6000533360006000600060206000a4')
            
        acc_balance = constraints.new_bitvec(256, name='balance_0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6')
        constraints.add(acc_balance == 100000000000000000000000)

        acc_nonce = constraints.new_bitvec(256, name='nonce_0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6')
        constraints.add(acc_nonce == 0)

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        caller = 0xcd1722f3947def4cf144679da39c4c32bdc35681
        price = constraints.new_bitvec(256, name='price')
        constraints.add(price == 100000000000000)

        value = constraints.new_bitvec(256, name='value')
        constraints.add(value == 1000000000000000000)

        gas = constraints.new_bitvec(256, name='gas')
        constraints.add(gas == 100000)

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
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('60ff6000533360006000600060206000a4'))
        # check outs
        self.assertEqual(returndata, unhexlify(''))
        # check logs
        logs = [Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs]
        data = rlp.encode(logs)
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '35f9d89d15631c07c9fe9938cbb68c24829193d66435373f55f924c906b854a4')

        # test used gas
        self.assertEqual(solve(world.current_vm.gas), 97840)

    def test_log4_logMemsizeTooHigh(self):
        """
        Textcase taken from https://github.com/ethereum/tests
        File: log4_logMemsizeTooHigh.json
        sha256sum: 1b16182821d84253995ac16cdfc907976c3dc0597b9199fc42c81edcec4c13c3
        Code:     PUSH32 0xaabbffffffffffffffffffffffffffffffffffffffffffffffffffffffffccdd
                  PUSH1 0x0
                  MSTORE
                  PUSH1 0x0
                  PUSH1 0x0
                  PUSH1 0x0
                  PUSH1 0x0
                  PUSH32 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
                  PUSH1 0x1
                  LOG4
        """    
    
        solver = Z3Solver()

        def solve(val):
            results = solver.get_all_values(constraints, val)
            # We constrain all values to single values!
            self.assertEqual(len(results), 1)
            return results[0]

        constraints = ConstraintSet()

        blocknumber = constraints.new_bitvec(256, name='blocknumber')
        constraints.add(blocknumber == 0)

        timestamp = constraints.new_bitvec(256, name='timestamp')
        constraints.add(timestamp == 1)

        difficulty = constraints.new_bitvec(256, name='difficulty')
        constraints.add(difficulty == 256)

        coinbase = constraints.new_bitvec(256, name='coinbase')
        constraints.add(coinbase == 244687034288125203496486448490407391986876152250)

        gaslimit = constraints.new_bitvec(256, name='gaslimit')
        constraints.add(gaslimit == 1000000)

        world = evm.EVMWorld(constraints, blocknumber=blocknumber, timestamp=timestamp, difficulty=difficulty,
                             coinbase=coinbase, gaslimit=gaslimit)
    
        acc_addr = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        acc_code = unhexlify('7faabbffffffffffffffffffffffffffffffffffffffffffffffffffffffffccdd60005260006000600060007fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff6001a4')
            
        acc_balance = constraints.new_bitvec(256, name='balance_0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6')
        constraints.add(acc_balance == 100000000000000000000000)

        acc_nonce = constraints.new_bitvec(256, name='nonce_0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6')
        constraints.add(acc_nonce == 0)

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        caller = 0xcd1722f3947def4cf144679da39c4c32bdc35681
        price = constraints.new_bitvec(256, name='price')
        constraints.add(price == 100000000000000)

        value = constraints.new_bitvec(256, name='value')
        constraints.add(value == 1000000000000000000)

        gas = constraints.new_bitvec(256, name='gas')
        constraints.add(gas == 100000)

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

        # If test end in exception check it here
        self.assertTrue(result == 'THROW')

    def test_log4_nonEmptyMem(self):
        """
        Textcase taken from https://github.com/ethereum/tests
        File: log4_nonEmptyMem.json
        sha256sum: f514d9d713ed720f4b6e3b4ff8bb9a12a57f1d6142d900c04000555b654a6230
        Code:     PUSH32 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
                  PUSH1 0x0
                  MSTORE
                  PUSH1 0x0
                  PUSH1 0x0
                  PUSH1 0x0
                  PUSH1 0x0
                  PUSH1 0x20
                  PUSH1 0x0
                  LOG4
        """    
    
        solver = Z3Solver()

        def solve(val):
            results = solver.get_all_values(constraints, val)
            # We constrain all values to single values!
            self.assertEqual(len(results), 1)
            return results[0]

        constraints = ConstraintSet()

        blocknumber = constraints.new_bitvec(256, name='blocknumber')
        constraints.add(blocknumber == 0)

        timestamp = constraints.new_bitvec(256, name='timestamp')
        constraints.add(timestamp == 1)

        difficulty = constraints.new_bitvec(256, name='difficulty')
        constraints.add(difficulty == 256)

        coinbase = constraints.new_bitvec(256, name='coinbase')
        constraints.add(coinbase == 244687034288125203496486448490407391986876152250)

        gaslimit = constraints.new_bitvec(256, name='gaslimit')
        constraints.add(gaslimit == 1000000)

        world = evm.EVMWorld(constraints, blocknumber=blocknumber, timestamp=timestamp, difficulty=difficulty,
                             coinbase=coinbase, gaslimit=gaslimit)
    
        acc_addr = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        acc_code = unhexlify('7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff600052600060006000600060206000a4')
            
        acc_balance = constraints.new_bitvec(256, name='balance_0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6')
        constraints.add(acc_balance == 100000000000000000000000)

        acc_nonce = constraints.new_bitvec(256, name='nonce_0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6')
        constraints.add(acc_nonce == 0)

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        caller = 0xcd1722f3947def4cf144679da39c4c32bdc35681
        price = constraints.new_bitvec(256, name='price')
        constraints.add(price == 100000000000000)

        value = constraints.new_bitvec(256, name='value')
        constraints.add(value == 1000000000000000000)

        gas = constraints.new_bitvec(256, name='gas')
        constraints.add(gas == 100000)

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
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff600052600060006000600060206000a4'))
        # check outs
        self.assertEqual(returndata, unhexlify(''))
        # check logs
        logs = [Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs]
        data = rlp.encode(logs)
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '0a0784a78d4f43441675b9f00e6ad4a313c9e57a6a01a6f49b8a890805857d8d')

        # test used gas
        self.assertEqual(solve(world.current_vm.gas), 97839)

    def test_log1_MaxTopic(self):
        """
        Textcase taken from https://github.com/ethereum/tests
        File: log1_MaxTopic.json
        sha256sum: 57461de16f0dd59bfb3e68a8f703148e0a4a86e77dbfc28db9b6b6eebb3a3e64
        Code:     PUSH32 0xaabbffffffffffffffffffffffffffffffffffffffffffffffffffffffffccdd
                  PUSH1 0x0
                  MSTORE
                  PUSH32 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
                  PUSH1 0x20
                  PUSH1 0x0
                  LOG1
        """    
    
        solver = Z3Solver()

        def solve(val):
            results = solver.get_all_values(constraints, val)
            # We constrain all values to single values!
            self.assertEqual(len(results), 1)
            return results[0]

        constraints = ConstraintSet()

        blocknumber = constraints.new_bitvec(256, name='blocknumber')
        constraints.add(blocknumber == 0)

        timestamp = constraints.new_bitvec(256, name='timestamp')
        constraints.add(timestamp == 1)

        difficulty = constraints.new_bitvec(256, name='difficulty')
        constraints.add(difficulty == 256)

        coinbase = constraints.new_bitvec(256, name='coinbase')
        constraints.add(coinbase == 244687034288125203496486448490407391986876152250)

        gaslimit = constraints.new_bitvec(256, name='gaslimit')
        constraints.add(gaslimit == 1000000)

        world = evm.EVMWorld(constraints, blocknumber=blocknumber, timestamp=timestamp, difficulty=difficulty,
                             coinbase=coinbase, gaslimit=gaslimit)
    
        acc_addr = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        acc_code = unhexlify('7faabbffffffffffffffffffffffffffffffffffffffffffffffffffffffffccdd6000527fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff60206000a1')
            
        acc_balance = constraints.new_bitvec(256, name='balance_0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6')
        constraints.add(acc_balance == 100000000000000000000000)

        acc_nonce = constraints.new_bitvec(256, name='nonce_0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6')
        constraints.add(acc_nonce == 0)

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        caller = 0xcd1722f3947def4cf144679da39c4c32bdc35681
        price = constraints.new_bitvec(256, name='price')
        constraints.add(price == 100000000000000)

        value = constraints.new_bitvec(256, name='value')
        constraints.add(value == 1000000000000000000)

        gas = constraints.new_bitvec(256, name='gas')
        constraints.add(gas == 100000)

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
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('7faabbffffffffffffffffffffffffffffffffffffffffffffffffffffffffccdd6000527fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff60206000a1'))
        # check outs
        self.assertEqual(returndata, unhexlify(''))
        # check logs
        logs = [Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs]
        data = rlp.encode(logs)
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '390a7f435e94b10f36ab57ca7106029629ee62569ed1bc309de88acc3ddfd954')

        # test used gas
        self.assertEqual(solve(world.current_vm.gas), 98973)

    def test_log3_logMemsizeTooHigh(self):
        """
        Textcase taken from https://github.com/ethereum/tests
        File: log3_logMemsizeTooHigh.json
        sha256sum: b9b8c6ab21dce6a1097155fc1ff6898983342a3e12d6742a89915a4458516454
        Code:     PUSH32 0xaabbffffffffffffffffffffffffffffffffffffffffffffffffffffffffccdd
                  PUSH1 0x0
                  MSTORE
                  PUSH1 0x0
                  PUSH1 0x0
                  PUSH1 0x0
                  PUSH32 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
                  PUSH1 0x1
                  LOG3
        """    
    
        solver = Z3Solver()

        def solve(val):
            results = solver.get_all_values(constraints, val)
            # We constrain all values to single values!
            self.assertEqual(len(results), 1)
            return results[0]

        constraints = ConstraintSet()

        blocknumber = constraints.new_bitvec(256, name='blocknumber')
        constraints.add(blocknumber == 0)

        timestamp = constraints.new_bitvec(256, name='timestamp')
        constraints.add(timestamp == 1)

        difficulty = constraints.new_bitvec(256, name='difficulty')
        constraints.add(difficulty == 256)

        coinbase = constraints.new_bitvec(256, name='coinbase')
        constraints.add(coinbase == 244687034288125203496486448490407391986876152250)

        gaslimit = constraints.new_bitvec(256, name='gaslimit')
        constraints.add(gaslimit == 1000000)

        world = evm.EVMWorld(constraints, blocknumber=blocknumber, timestamp=timestamp, difficulty=difficulty,
                             coinbase=coinbase, gaslimit=gaslimit)
    
        acc_addr = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        acc_code = unhexlify('7faabbffffffffffffffffffffffffffffffffffffffffffffffffffffffffccdd6000526000600060007fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff6001a3')
            
        acc_balance = constraints.new_bitvec(256, name='balance_0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6')
        constraints.add(acc_balance == 100000000000000000000000)

        acc_nonce = constraints.new_bitvec(256, name='nonce_0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6')
        constraints.add(acc_nonce == 0)

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        caller = 0xcd1722f3947def4cf144679da39c4c32bdc35681
        price = constraints.new_bitvec(256, name='price')
        constraints.add(price == 100000000000000)

        value = constraints.new_bitvec(256, name='value')
        constraints.add(value == 1000000000000000000)

        gas = constraints.new_bitvec(256, name='gas')
        constraints.add(gas == 100000)

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

        # If test end in exception check it here
        self.assertTrue(result == 'THROW')

    def test_log3_PC(self):
        """
        Textcase taken from https://github.com/ethereum/tests
        File: log3_PC.json
        sha256sum: 7c7bfdc8d5cd97b8861635f6bf033686ed2db90b0738a007774780963d1ecf6f
        Code:     PUSH1 0xff
                  PUSH1 0x0
                  MSTORE8
                  GETPC
                  GETPC
                  GETPC
                  PUSH1 0x20
                  PUSH1 0x0
                  LOG3
        """    
    
        solver = Z3Solver()

        def solve(val):
            results = solver.get_all_values(constraints, val)
            # We constrain all values to single values!
            self.assertEqual(len(results), 1)
            return results[0]

        constraints = ConstraintSet()

        blocknumber = constraints.new_bitvec(256, name='blocknumber')
        constraints.add(blocknumber == 0)

        timestamp = constraints.new_bitvec(256, name='timestamp')
        constraints.add(timestamp == 1)

        difficulty = constraints.new_bitvec(256, name='difficulty')
        constraints.add(difficulty == 256)

        coinbase = constraints.new_bitvec(256, name='coinbase')
        constraints.add(coinbase == 244687034288125203496486448490407391986876152250)

        gaslimit = constraints.new_bitvec(256, name='gaslimit')
        constraints.add(gaslimit == 1000000)

        world = evm.EVMWorld(constraints, blocknumber=blocknumber, timestamp=timestamp, difficulty=difficulty,
                             coinbase=coinbase, gaslimit=gaslimit)
    
        acc_addr = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        acc_code = unhexlify('60ff60005358585860206000a3')
            
        acc_balance = constraints.new_bitvec(256, name='balance_0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6')
        constraints.add(acc_balance == 100000000000000000000000)

        acc_nonce = constraints.new_bitvec(256, name='nonce_0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6')
        constraints.add(acc_nonce == 0)

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        caller = 0xcd1722f3947def4cf144679da39c4c32bdc35681
        price = constraints.new_bitvec(256, name='price')
        constraints.add(price == 100000000000000)

        value = constraints.new_bitvec(256, name='value')
        constraints.add(value == 1000000000000000000)

        gas = constraints.new_bitvec(256, name='gas')
        constraints.add(gas == 100000)

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
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('60ff60005358585860206000a3'))
        # check outs
        self.assertEqual(returndata, unhexlify(''))
        # check logs
        logs = [Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs]
        data = rlp.encode(logs)
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '7cee1faf751b1e6b79f5a9c8b4ce8d5b8d1ce5cbc1960336f1edf7800242d880')

        # test used gas
        self.assertEqual(solve(world.current_vm.gas), 98220)

    def test_log3_nonEmptyMem_logMemSize1_logMemStart31(self):
        """
        Textcase taken from https://github.com/ethereum/tests
        File: log3_nonEmptyMem_logMemSize1_logMemStart31.json
        sha256sum: e51d3a9329e2c7f99519988e90a237710113a929d05abc6f11aa2e41bd244ebe
        Code:     PUSH32 0xaabbffffffffffffffffffffffffffffffffffffffffffffffffffffffffccdd
                  PUSH1 0x0
                  MSTORE
                  PUSH1 0x0
                  PUSH1 0x0
                  PUSH1 0x0
                  PUSH1 0x1
                  PUSH1 0x1f
                  LOG3
        """    
    
        solver = Z3Solver()

        def solve(val):
            results = solver.get_all_values(constraints, val)
            # We constrain all values to single values!
            self.assertEqual(len(results), 1)
            return results[0]

        constraints = ConstraintSet()

        blocknumber = constraints.new_bitvec(256, name='blocknumber')
        constraints.add(blocknumber == 0)

        timestamp = constraints.new_bitvec(256, name='timestamp')
        constraints.add(timestamp == 1)

        difficulty = constraints.new_bitvec(256, name='difficulty')
        constraints.add(difficulty == 256)

        coinbase = constraints.new_bitvec(256, name='coinbase')
        constraints.add(coinbase == 244687034288125203496486448490407391986876152250)

        gaslimit = constraints.new_bitvec(256, name='gaslimit')
        constraints.add(gaslimit == 1000000)

        world = evm.EVMWorld(constraints, blocknumber=blocknumber, timestamp=timestamp, difficulty=difficulty,
                             coinbase=coinbase, gaslimit=gaslimit)
    
        acc_addr = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        acc_code = unhexlify('7faabbffffffffffffffffffffffffffffffffffffffffffffffffffffffffccdd6000526000600060006001601fa3')
            
        acc_balance = constraints.new_bitvec(256, name='balance_0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6')
        constraints.add(acc_balance == 100000000000000000000000)

        acc_nonce = constraints.new_bitvec(256, name='nonce_0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6')
        constraints.add(acc_nonce == 0)

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        caller = 0xcd1722f3947def4cf144679da39c4c32bdc35681
        price = constraints.new_bitvec(256, name='price')
        constraints.add(price == 100000000000000)

        value = constraints.new_bitvec(256, name='value')
        constraints.add(value == 1000000000000000000)

        gas = constraints.new_bitvec(256, name='gas')
        constraints.add(gas == 100000)

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
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('7faabbffffffffffffffffffffffffffffffffffffffffffffffffffffffffccdd6000526000600060006001601fa3'))
        # check outs
        self.assertEqual(returndata, unhexlify(''))
        # check logs
        logs = [Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs]
        data = rlp.encode(logs)
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '56733300bf7f644b82e00b314f1cfc0ac057f6dfc6a2b821970423603a44889f')

        # test used gas
        self.assertEqual(solve(world.current_vm.gas), 98465)

    def test_log3_logMemStartTooHigh(self):
        """
        Textcase taken from https://github.com/ethereum/tests
        File: log3_logMemStartTooHigh.json
        sha256sum: 5d7a20fbe12cd1563bba812df671f2bb56890fb3093aca942427c6e47efec21b
        Code:     PUSH32 0xaabbffffffffffffffffffffffffffffffffffffffffffffffffffffffffccdd
                  PUSH1 0x0
                  MSTORE
                  PUSH1 0x0
                  PUSH1 0x0
                  PUSH1 0x0
                  PUSH1 0x1
                  PUSH32 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
                  LOG3
        """    
    
        solver = Z3Solver()

        def solve(val):
            results = solver.get_all_values(constraints, val)
            # We constrain all values to single values!
            self.assertEqual(len(results), 1)
            return results[0]

        constraints = ConstraintSet()

        blocknumber = constraints.new_bitvec(256, name='blocknumber')
        constraints.add(blocknumber == 0)

        timestamp = constraints.new_bitvec(256, name='timestamp')
        constraints.add(timestamp == 1)

        difficulty = constraints.new_bitvec(256, name='difficulty')
        constraints.add(difficulty == 256)

        coinbase = constraints.new_bitvec(256, name='coinbase')
        constraints.add(coinbase == 244687034288125203496486448490407391986876152250)

        gaslimit = constraints.new_bitvec(256, name='gaslimit')
        constraints.add(gaslimit == 1000000)

        world = evm.EVMWorld(constraints, blocknumber=blocknumber, timestamp=timestamp, difficulty=difficulty,
                             coinbase=coinbase, gaslimit=gaslimit)
    
        acc_addr = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        acc_code = unhexlify('7faabbffffffffffffffffffffffffffffffffffffffffffffffffffffffffccdd60005260006000600060017fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffa3')
            
        acc_balance = constraints.new_bitvec(256, name='balance_0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6')
        constraints.add(acc_balance == 100000000000000000000000)

        acc_nonce = constraints.new_bitvec(256, name='nonce_0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6')
        constraints.add(acc_nonce == 0)

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        caller = 0xcd1722f3947def4cf144679da39c4c32bdc35681
        price = constraints.new_bitvec(256, name='price')
        constraints.add(price == 100000000000000)

        value = constraints.new_bitvec(256, name='value')
        constraints.add(value == 1000000000000000000)

        gas = constraints.new_bitvec(256, name='gas')
        constraints.add(gas == 100000)

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

        # If test end in exception check it here
        self.assertTrue(result == 'THROW')

    def test_log1_nonEmptyMem_logMemSize1(self):
        """
        Textcase taken from https://github.com/ethereum/tests
        File: log1_nonEmptyMem_logMemSize1.json
        sha256sum: ac8beeadb21036f2a2f1f0a89489816082f37c74c1fc9371885120d6418ab9cd
        Code:     PUSH32 0xaabbffffffffffffffffffffffffffffffffffffffffffffffffffffffffccdd
                  PUSH1 0x0
                  MSTORE
                  PUSH1 0x0
                  PUSH1 0x1
                  PUSH1 0x0
                  LOG1
        """    
    
        solver = Z3Solver()

        def solve(val):
            results = solver.get_all_values(constraints, val)
            # We constrain all values to single values!
            self.assertEqual(len(results), 1)
            return results[0]

        constraints = ConstraintSet()

        blocknumber = constraints.new_bitvec(256, name='blocknumber')
        constraints.add(blocknumber == 0)

        timestamp = constraints.new_bitvec(256, name='timestamp')
        constraints.add(timestamp == 1)

        difficulty = constraints.new_bitvec(256, name='difficulty')
        constraints.add(difficulty == 256)

        coinbase = constraints.new_bitvec(256, name='coinbase')
        constraints.add(coinbase == 244687034288125203496486448490407391986876152250)

        gaslimit = constraints.new_bitvec(256, name='gaslimit')
        constraints.add(gaslimit == 1000000)

        world = evm.EVMWorld(constraints, blocknumber=blocknumber, timestamp=timestamp, difficulty=difficulty,
                             coinbase=coinbase, gaslimit=gaslimit)
    
        acc_addr = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        acc_code = unhexlify('7faabbffffffffffffffffffffffffffffffffffffffffffffffffffffffffccdd600052600060016000a1')
            
        acc_balance = constraints.new_bitvec(256, name='balance_0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6')
        constraints.add(acc_balance == 100000000000000000000000)

        acc_nonce = constraints.new_bitvec(256, name='nonce_0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6')
        constraints.add(acc_nonce == 0)

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        caller = 0xcd1722f3947def4cf144679da39c4c32bdc35681
        price = constraints.new_bitvec(256, name='price')
        constraints.add(price == 100000000000000)

        value = constraints.new_bitvec(256, name='value')
        constraints.add(value == 1000000000000000000)

        gas = constraints.new_bitvec(256, name='gas')
        constraints.add(gas == 100000)

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
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('7faabbffffffffffffffffffffffffffffffffffffffffffffffffffffffffccdd600052600060016000a1'))
        # check outs
        self.assertEqual(returndata, unhexlify(''))
        # check logs
        logs = [Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs]
        data = rlp.encode(logs)
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '5bb955226d045691dc50a5adb050b48e9167abcf287e5a65e67c69635b4a84a2')

        # test used gas
        self.assertEqual(solve(world.current_vm.gas), 99221)

    def test_log4_MaxTopic(self):
        """
        Textcase taken from https://github.com/ethereum/tests
        File: log4_MaxTopic.json
        sha256sum: 142cbb9192a5d11222e05532bb8a1bacac8760bcf3f7971a5e6a155e23a36200
        Code:     PUSH32 0xaabbffffffffffffffffffffffffffffffffffffffffffffffffffffffffccdd
                  PUSH1 0x0
                  MSTORE
                  PUSH32 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
                  PUSH32 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
                  PUSH32 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
                  PUSH32 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
                  PUSH1 0x20
                  PUSH1 0x0
                  LOG4
        """    
    
        solver = Z3Solver()

        def solve(val):
            results = solver.get_all_values(constraints, val)
            # We constrain all values to single values!
            self.assertEqual(len(results), 1)
            return results[0]

        constraints = ConstraintSet()

        blocknumber = constraints.new_bitvec(256, name='blocknumber')
        constraints.add(blocknumber == 0)

        timestamp = constraints.new_bitvec(256, name='timestamp')
        constraints.add(timestamp == 1)

        difficulty = constraints.new_bitvec(256, name='difficulty')
        constraints.add(difficulty == 256)

        coinbase = constraints.new_bitvec(256, name='coinbase')
        constraints.add(coinbase == 244687034288125203496486448490407391986876152250)

        gaslimit = constraints.new_bitvec(256, name='gaslimit')
        constraints.add(gaslimit == 1000000)

        world = evm.EVMWorld(constraints, blocknumber=blocknumber, timestamp=timestamp, difficulty=difficulty,
                             coinbase=coinbase, gaslimit=gaslimit)
    
        acc_addr = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        acc_code = unhexlify('7faabbffffffffffffffffffffffffffffffffffffffffffffffffffffffffccdd6000527fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff60206000a4')
            
        acc_balance = constraints.new_bitvec(256, name='balance_0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6')
        constraints.add(acc_balance == 100000000000000000000000)

        acc_nonce = constraints.new_bitvec(256, name='nonce_0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6')
        constraints.add(acc_nonce == 0)

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        caller = 0xcd1722f3947def4cf144679da39c4c32bdc35681
        price = constraints.new_bitvec(256, name='price')
        constraints.add(price == 100000000000000)

        value = constraints.new_bitvec(256, name='value')
        constraints.add(value == 1000000000000000000)

        gas = constraints.new_bitvec(256, name='gas')
        constraints.add(gas == 100000)

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
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('7faabbffffffffffffffffffffffffffffffffffffffffffffffffffffffffccdd6000527fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff60206000a4'))
        # check outs
        self.assertEqual(returndata, unhexlify(''))
        # check logs
        logs = [Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs]
        data = rlp.encode(logs)
        self.assertEqual(sha3.keccak_256(data).hexdigest(), 'ef71a715e664cf4bfc47d7cc5c7b32a046c0092570e8048742f60fe3232b168a')

        # test used gas
        self.assertEqual(solve(world.current_vm.gas), 97839)

    def test_log3_Caller(self):
        """
        Textcase taken from https://github.com/ethereum/tests
        File: log3_Caller.json
        sha256sum: 870701b94ec1859d68b65f9a8ad3da38481b90d051ce097207fd6681b3dcf7e6
        Code:     PUSH1 0xff
                  PUSH1 0x0
                  MSTORE8
                  CALLER
                  PUSH1 0x0
                  PUSH1 0x0
                  PUSH1 0x20
                  PUSH1 0x0
                  LOG3
        """    
    
        solver = Z3Solver()

        def solve(val):
            results = solver.get_all_values(constraints, val)
            # We constrain all values to single values!
            self.assertEqual(len(results), 1)
            return results[0]

        constraints = ConstraintSet()

        blocknumber = constraints.new_bitvec(256, name='blocknumber')
        constraints.add(blocknumber == 0)

        timestamp = constraints.new_bitvec(256, name='timestamp')
        constraints.add(timestamp == 1)

        difficulty = constraints.new_bitvec(256, name='difficulty')
        constraints.add(difficulty == 256)

        coinbase = constraints.new_bitvec(256, name='coinbase')
        constraints.add(coinbase == 244687034288125203496486448490407391986876152250)

        gaslimit = constraints.new_bitvec(256, name='gaslimit')
        constraints.add(gaslimit == 1000000)

        world = evm.EVMWorld(constraints, blocknumber=blocknumber, timestamp=timestamp, difficulty=difficulty,
                             coinbase=coinbase, gaslimit=gaslimit)
    
        acc_addr = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        acc_code = unhexlify('60ff600053336000600060206000a3')
            
        acc_balance = constraints.new_bitvec(256, name='balance_0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6')
        constraints.add(acc_balance == 100000000000000000000000)

        acc_nonce = constraints.new_bitvec(256, name='nonce_0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6')
        constraints.add(acc_nonce == 0)

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        caller = 0xcd1722f3947def4cf144679da39c4c32bdc35681
        price = constraints.new_bitvec(256, name='price')
        constraints.add(price == 100000000000000)

        value = constraints.new_bitvec(256, name='value')
        constraints.add(value == 1000000000000000000)

        gas = constraints.new_bitvec(256, name='gas')
        constraints.add(gas == 100000)

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
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('60ff600053336000600060206000a3'))
        # check outs
        self.assertEqual(returndata, unhexlify(''))
        # check logs
        logs = [Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs]
        data = rlp.encode(logs)
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '3e85bcf5ae0e8017697b1668fe3133293de024a46c44194f6345f66a4bd32023')

        # test used gas
        self.assertEqual(solve(world.current_vm.gas), 98218)

    def test_log3_nonEmptyMem(self):
        """
        Textcase taken from https://github.com/ethereum/tests
        File: log3_nonEmptyMem.json
        sha256sum: d40e559cce1ff7bc5b8a01190a3ea0b672856c59627720654b300535bda94349
        Code:     PUSH32 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
                  PUSH1 0x0
                  MSTORE
                  PUSH1 0x0
                  PUSH1 0x0
                  PUSH1 0x0
                  PUSH1 0x20
                  PUSH1 0x0
                  LOG3
        """    
    
        solver = Z3Solver()

        def solve(val):
            results = solver.get_all_values(constraints, val)
            # We constrain all values to single values!
            self.assertEqual(len(results), 1)
            return results[0]

        constraints = ConstraintSet()

        blocknumber = constraints.new_bitvec(256, name='blocknumber')
        constraints.add(blocknumber == 0)

        timestamp = constraints.new_bitvec(256, name='timestamp')
        constraints.add(timestamp == 1)

        difficulty = constraints.new_bitvec(256, name='difficulty')
        constraints.add(difficulty == 256)

        coinbase = constraints.new_bitvec(256, name='coinbase')
        constraints.add(coinbase == 244687034288125203496486448490407391986876152250)

        gaslimit = constraints.new_bitvec(256, name='gaslimit')
        constraints.add(gaslimit == 1000000)

        world = evm.EVMWorld(constraints, blocknumber=blocknumber, timestamp=timestamp, difficulty=difficulty,
                             coinbase=coinbase, gaslimit=gaslimit)
    
        acc_addr = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        acc_code = unhexlify('7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff60005260006000600060206000a3')
            
        acc_balance = constraints.new_bitvec(256, name='balance_0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6')
        constraints.add(acc_balance == 100000000000000000000000)

        acc_nonce = constraints.new_bitvec(256, name='nonce_0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6')
        constraints.add(acc_nonce == 0)

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        caller = 0xcd1722f3947def4cf144679da39c4c32bdc35681
        price = constraints.new_bitvec(256, name='price')
        constraints.add(price == 100000000000000)

        value = constraints.new_bitvec(256, name='value')
        constraints.add(value == 1000000000000000000)

        gas = constraints.new_bitvec(256, name='gas')
        constraints.add(gas == 100000)

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
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff60005260006000600060206000a3'))
        # check outs
        self.assertEqual(returndata, unhexlify(''))
        # check logs
        logs = [Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs]
        data = rlp.encode(logs)
        self.assertEqual(sha3.keccak_256(data).hexdigest(), 'b9cdb22df321bb4d58b94e6928f3db861ceff5fbc398e12675b9027add956f49')

        # test used gas
        self.assertEqual(solve(world.current_vm.gas), 98217)

    def test_log3_MaxTopic(self):
        """
        Textcase taken from https://github.com/ethereum/tests
        File: log3_MaxTopic.json
        sha256sum: d4237a1127f783c8865177e496afb3318135b4bf3e032d84bc33f69a8fa6281f
        Code:     PUSH32 0xaabbffffffffffffffffffffffffffffffffffffffffffffffffffffffffccdd
                  PUSH1 0x0
                  MSTORE
                  PUSH32 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
                  PUSH32 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
                  PUSH32 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
                  PUSH1 0x20
                  PUSH1 0x0
                  LOG3
        """    
    
        solver = Z3Solver()

        def solve(val):
            results = solver.get_all_values(constraints, val)
            # We constrain all values to single values!
            self.assertEqual(len(results), 1)
            return results[0]

        constraints = ConstraintSet()

        blocknumber = constraints.new_bitvec(256, name='blocknumber')
        constraints.add(blocknumber == 0)

        timestamp = constraints.new_bitvec(256, name='timestamp')
        constraints.add(timestamp == 1)

        difficulty = constraints.new_bitvec(256, name='difficulty')
        constraints.add(difficulty == 256)

        coinbase = constraints.new_bitvec(256, name='coinbase')
        constraints.add(coinbase == 244687034288125203496486448490407391986876152250)

        gaslimit = constraints.new_bitvec(256, name='gaslimit')
        constraints.add(gaslimit == 1000000)

        world = evm.EVMWorld(constraints, blocknumber=blocknumber, timestamp=timestamp, difficulty=difficulty,
                             coinbase=coinbase, gaslimit=gaslimit)
    
        acc_addr = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        acc_code = unhexlify('7faabbffffffffffffffffffffffffffffffffffffffffffffffffffffffffccdd6000527fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff60206000a3')
            
        acc_balance = constraints.new_bitvec(256, name='balance_0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6')
        constraints.add(acc_balance == 100000000000000000000000)

        acc_nonce = constraints.new_bitvec(256, name='nonce_0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6')
        constraints.add(acc_nonce == 0)

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        caller = 0xcd1722f3947def4cf144679da39c4c32bdc35681
        price = constraints.new_bitvec(256, name='price')
        constraints.add(price == 100000000000000)

        value = constraints.new_bitvec(256, name='value')
        constraints.add(value == 1000000000000000000)

        gas = constraints.new_bitvec(256, name='gas')
        constraints.add(gas == 100000)

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
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('7faabbffffffffffffffffffffffffffffffffffffffffffffffffffffffffccdd6000527fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff60206000a3'))
        # check outs
        self.assertEqual(returndata, unhexlify(''))
        # check logs
        logs = [Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs]
        data = rlp.encode(logs)
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '486418c45425c02eee174815dcc8d611111e35ddc111d7cf61660376629ee9f4')

        # test used gas
        self.assertEqual(solve(world.current_vm.gas), 98217)

    def test_log1_nonEmptyMem_logMemSize1_logMemStart31(self):
        """
        Textcase taken from https://github.com/ethereum/tests
        File: log1_nonEmptyMem_logMemSize1_logMemStart31.json
        sha256sum: 370157a2cd11135c86b27f5f4b75b1aafe088ed0b65afcce1346a4fdb6fd59a6
        Code:     PUSH32 0xaabbffffffffffffffffffffffffffffffffffffffffffffffffffffffffccdd
                  PUSH1 0x0
                  MSTORE
                  PUSH1 0x0
                  PUSH1 0x1
                  PUSH1 0x1f
                  LOG1
        """    
    
        solver = Z3Solver()

        def solve(val):
            results = solver.get_all_values(constraints, val)
            # We constrain all values to single values!
            self.assertEqual(len(results), 1)
            return results[0]

        constraints = ConstraintSet()

        blocknumber = constraints.new_bitvec(256, name='blocknumber')
        constraints.add(blocknumber == 0)

        timestamp = constraints.new_bitvec(256, name='timestamp')
        constraints.add(timestamp == 1)

        difficulty = constraints.new_bitvec(256, name='difficulty')
        constraints.add(difficulty == 256)

        coinbase = constraints.new_bitvec(256, name='coinbase')
        constraints.add(coinbase == 244687034288125203496486448490407391986876152250)

        gaslimit = constraints.new_bitvec(256, name='gaslimit')
        constraints.add(gaslimit == 1000000)

        world = evm.EVMWorld(constraints, blocknumber=blocknumber, timestamp=timestamp, difficulty=difficulty,
                             coinbase=coinbase, gaslimit=gaslimit)
    
        acc_addr = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        acc_code = unhexlify('7faabbffffffffffffffffffffffffffffffffffffffffffffffffffffffffccdd60005260006001601fa1')
            
        acc_balance = constraints.new_bitvec(256, name='balance_0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6')
        constraints.add(acc_balance == 100000000000000000000000)

        acc_nonce = constraints.new_bitvec(256, name='nonce_0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6')
        constraints.add(acc_nonce == 0)

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        caller = 0xcd1722f3947def4cf144679da39c4c32bdc35681
        price = constraints.new_bitvec(256, name='price')
        constraints.add(price == 100000000000000)

        value = constraints.new_bitvec(256, name='value')
        constraints.add(value == 1000000000000000000)

        gas = constraints.new_bitvec(256, name='gas')
        constraints.add(gas == 100000)

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
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('7faabbffffffffffffffffffffffffffffffffffffffffffffffffffffffffccdd60005260006001601fa1'))
        # check outs
        self.assertEqual(returndata, unhexlify(''))
        # check logs
        logs = [Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs]
        data = rlp.encode(logs)
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '3e9e84d955681613494d5aa93b50bb45e9a1b38791a7292667f88dd56d9a442d')

        # test used gas
        self.assertEqual(solve(world.current_vm.gas), 99221)

    def test_log2_nonEmptyMem_logMemSize1(self):
        """
        Textcase taken from https://github.com/ethereum/tests
        File: log2_nonEmptyMem_logMemSize1.json
        sha256sum: fa27492be41be53c5924bc55047254efa6b1fa214276707bc04a32ad1abbc335
        Code:     PUSH32 0xaabbffffffffffffffffffffffffffffffffffffffffffffffffffffffffccdd
                  PUSH1 0x0
                  MSTORE
                  PUSH1 0x0
                  PUSH1 0x0
                  PUSH1 0x1
                  PUSH1 0x0
                  LOG2
        """    
    
        solver = Z3Solver()

        def solve(val):
            results = solver.get_all_values(constraints, val)
            # We constrain all values to single values!
            self.assertEqual(len(results), 1)
            return results[0]

        constraints = ConstraintSet()

        blocknumber = constraints.new_bitvec(256, name='blocknumber')
        constraints.add(blocknumber == 0)

        timestamp = constraints.new_bitvec(256, name='timestamp')
        constraints.add(timestamp == 1)

        difficulty = constraints.new_bitvec(256, name='difficulty')
        constraints.add(difficulty == 256)

        coinbase = constraints.new_bitvec(256, name='coinbase')
        constraints.add(coinbase == 244687034288125203496486448490407391986876152250)

        gaslimit = constraints.new_bitvec(256, name='gaslimit')
        constraints.add(gaslimit == 1000000)

        world = evm.EVMWorld(constraints, blocknumber=blocknumber, timestamp=timestamp, difficulty=difficulty,
                             coinbase=coinbase, gaslimit=gaslimit)
    
        acc_addr = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        acc_code = unhexlify('7faabbffffffffffffffffffffffffffffffffffffffffffffffffffffffffccdd6000526000600060016000a2')
            
        acc_balance = constraints.new_bitvec(256, name='balance_0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6')
        constraints.add(acc_balance == 100000000000000000000000)

        acc_nonce = constraints.new_bitvec(256, name='nonce_0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6')
        constraints.add(acc_nonce == 0)

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        caller = 0xcd1722f3947def4cf144679da39c4c32bdc35681
        price = constraints.new_bitvec(256, name='price')
        constraints.add(price == 100000000000000)

        value = constraints.new_bitvec(256, name='value')
        constraints.add(value == 1000000000000000000)

        gas = constraints.new_bitvec(256, name='gas')
        constraints.add(gas == 100000)

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
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('7faabbffffffffffffffffffffffffffffffffffffffffffffffffffffffffccdd6000526000600060016000a2'))
        # check outs
        self.assertEqual(returndata, unhexlify(''))
        # check logs
        logs = [Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs]
        data = rlp.encode(logs)
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '45c138a1e810080c595869ef1ebed27c70c3d6fb48a3db0b5173b2053e787ef3')

        # test used gas
        self.assertEqual(solve(world.current_vm.gas), 98843)

    def test_log2_nonEmptyMem_logMemSize1_logMemStart31(self):
        """
        Textcase taken from https://github.com/ethereum/tests
        File: log2_nonEmptyMem_logMemSize1_logMemStart31.json
        sha256sum: c1ac8a117d47f2634a5a82e9256e38b6c6dd585c7322094927f01a66559a9023
        Code:     PUSH32 0xaabbffffffffffffffffffffffffffffffffffffffffffffffffffffffffccdd
                  PUSH1 0x0
                  MSTORE
                  PUSH1 0x0
                  PUSH1 0x0
                  PUSH1 0x1
                  PUSH1 0x1f
                  LOG2
        """    
    
        solver = Z3Solver()

        def solve(val):
            results = solver.get_all_values(constraints, val)
            # We constrain all values to single values!
            self.assertEqual(len(results), 1)
            return results[0]

        constraints = ConstraintSet()

        blocknumber = constraints.new_bitvec(256, name='blocknumber')
        constraints.add(blocknumber == 0)

        timestamp = constraints.new_bitvec(256, name='timestamp')
        constraints.add(timestamp == 1)

        difficulty = constraints.new_bitvec(256, name='difficulty')
        constraints.add(difficulty == 256)

        coinbase = constraints.new_bitvec(256, name='coinbase')
        constraints.add(coinbase == 244687034288125203496486448490407391986876152250)

        gaslimit = constraints.new_bitvec(256, name='gaslimit')
        constraints.add(gaslimit == 1000000)

        world = evm.EVMWorld(constraints, blocknumber=blocknumber, timestamp=timestamp, difficulty=difficulty,
                             coinbase=coinbase, gaslimit=gaslimit)
    
        acc_addr = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        acc_code = unhexlify('7faabbffffffffffffffffffffffffffffffffffffffffffffffffffffffffccdd600052600060006001601fa2')
            
        acc_balance = constraints.new_bitvec(256, name='balance_0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6')
        constraints.add(acc_balance == 100000000000000000000000)

        acc_nonce = constraints.new_bitvec(256, name='nonce_0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6')
        constraints.add(acc_nonce == 0)

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        caller = 0xcd1722f3947def4cf144679da39c4c32bdc35681
        price = constraints.new_bitvec(256, name='price')
        constraints.add(price == 100000000000000)

        value = constraints.new_bitvec(256, name='value')
        constraints.add(value == 1000000000000000000)

        gas = constraints.new_bitvec(256, name='gas')
        constraints.add(gas == 100000)

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
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('7faabbffffffffffffffffffffffffffffffffffffffffffffffffffffffffccdd600052600060006001601fa2'))
        # check outs
        self.assertEqual(returndata, unhexlify(''))
        # check logs
        logs = [Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs]
        data = rlp.encode(logs)
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '4409136ea4b71b7651f1c9c65efd0455ec856c93ce6295a1677ae7c3791e3c48')

        # test used gas
        self.assertEqual(solve(world.current_vm.gas), 98843)

    def test_log3_emptyMem(self):
        """
        Textcase taken from https://github.com/ethereum/tests
        File: log3_emptyMem.json
        sha256sum: e65b8aa71c00fed84051025311fb2839d57cd13e93cad54ff950af022b739fd7
        Code:     PUSH1 0x0
                  PUSH1 0x0
                  PUSH1 0x0
                  PUSH1 0x0
                  PUSH1 0x0
                  LOG3
        """    
    
        solver = Z3Solver()

        def solve(val):
            results = solver.get_all_values(constraints, val)
            # We constrain all values to single values!
            self.assertEqual(len(results), 1)
            return results[0]

        constraints = ConstraintSet()

        blocknumber = constraints.new_bitvec(256, name='blocknumber')
        constraints.add(blocknumber == 0)

        timestamp = constraints.new_bitvec(256, name='timestamp')
        constraints.add(timestamp == 1)

        difficulty = constraints.new_bitvec(256, name='difficulty')
        constraints.add(difficulty == 256)

        coinbase = constraints.new_bitvec(256, name='coinbase')
        constraints.add(coinbase == 244687034288125203496486448490407391986876152250)

        gaslimit = constraints.new_bitvec(256, name='gaslimit')
        constraints.add(gaslimit == 1000000)

        world = evm.EVMWorld(constraints, blocknumber=blocknumber, timestamp=timestamp, difficulty=difficulty,
                             coinbase=coinbase, gaslimit=gaslimit)
    
        acc_addr = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        acc_code = unhexlify('60006000600060006000a3')
            
        acc_balance = constraints.new_bitvec(256, name='balance_0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6')
        constraints.add(acc_balance == 100000000000000000000000)

        acc_nonce = constraints.new_bitvec(256, name='nonce_0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6')
        constraints.add(acc_nonce == 0)

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        caller = 0xcd1722f3947def4cf144679da39c4c32bdc35681
        price = constraints.new_bitvec(256, name='price')
        constraints.add(price == 100000000000000)

        value = constraints.new_bitvec(256, name='value')
        constraints.add(value == 1000000000000000000)

        gas = constraints.new_bitvec(256, name='gas')
        constraints.add(gas == 100000)

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
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('60006000600060006000a3'))
        # check outs
        self.assertEqual(returndata, unhexlify(''))
        # check logs
        logs = [Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs]
        data = rlp.encode(logs)
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '79f83975e7ea5efeeb8e2b08ea11bd9f320f34042ce7f2abd4df8a26b04839c0')

        # test used gas
        self.assertEqual(solve(world.current_vm.gas), 98485)

    def test_log4_logMemStartTooHigh(self):
        """
        Textcase taken from https://github.com/ethereum/tests
        File: log4_logMemStartTooHigh.json
        sha256sum: 6b053a6e0bbcc8aa6eaabf2d724c6393b9f58ecdd82413691c166308af70b58c
        Code:     PUSH32 0xaabbffffffffffffffffffffffffffffffffffffffffffffffffffffffffccdd
                  PUSH1 0x0
                  MSTORE
                  PUSH1 0x0
                  PUSH1 0x0
                  PUSH1 0x0
                  PUSH1 0x0
                  PUSH1 0x1
                  PUSH32 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
                  LOG4
        """    
    
        solver = Z3Solver()

        def solve(val):
            results = solver.get_all_values(constraints, val)
            # We constrain all values to single values!
            self.assertEqual(len(results), 1)
            return results[0]

        constraints = ConstraintSet()

        blocknumber = constraints.new_bitvec(256, name='blocknumber')
        constraints.add(blocknumber == 0)

        timestamp = constraints.new_bitvec(256, name='timestamp')
        constraints.add(timestamp == 1)

        difficulty = constraints.new_bitvec(256, name='difficulty')
        constraints.add(difficulty == 256)

        coinbase = constraints.new_bitvec(256, name='coinbase')
        constraints.add(coinbase == 244687034288125203496486448490407391986876152250)

        gaslimit = constraints.new_bitvec(256, name='gaslimit')
        constraints.add(gaslimit == 1000000)

        world = evm.EVMWorld(constraints, blocknumber=blocknumber, timestamp=timestamp, difficulty=difficulty,
                             coinbase=coinbase, gaslimit=gaslimit)
    
        acc_addr = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        acc_code = unhexlify('7faabbffffffffffffffffffffffffffffffffffffffffffffffffffffffffccdd600052600060006000600060017fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffa4')
            
        acc_balance = constraints.new_bitvec(256, name='balance_0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6')
        constraints.add(acc_balance == 100000000000000000000000)

        acc_nonce = constraints.new_bitvec(256, name='nonce_0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6')
        constraints.add(acc_nonce == 0)

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        caller = 0xcd1722f3947def4cf144679da39c4c32bdc35681
        price = constraints.new_bitvec(256, name='price')
        constraints.add(price == 100000000000000)

        value = constraints.new_bitvec(256, name='value')
        constraints.add(value == 1000000000000000000)

        gas = constraints.new_bitvec(256, name='gas')
        constraints.add(gas == 100000)

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

        # If test end in exception check it here
        self.assertTrue(result == 'THROW')

    def test_log4_nonEmptyMem_logMemSize1(self):
        """
        Textcase taken from https://github.com/ethereum/tests
        File: log4_nonEmptyMem_logMemSize1.json
        sha256sum: 49568a8bc0b0e4671ca0fd2721e1fd8159e48932c379c18398e47b7f61512d5e
        Code:     PUSH32 0xaabbffffffffffffffffffffffffffffffffffffffffffffffffffffffffccdd
                  PUSH1 0x0
                  MSTORE
                  PUSH1 0x0
                  PUSH1 0x0
                  PUSH1 0x0
                  PUSH1 0x0
                  PUSH1 0x1
                  PUSH1 0x0
                  LOG4
        """    
    
        solver = Z3Solver()

        def solve(val):
            results = solver.get_all_values(constraints, val)
            # We constrain all values to single values!
            self.assertEqual(len(results), 1)
            return results[0]

        constraints = ConstraintSet()

        blocknumber = constraints.new_bitvec(256, name='blocknumber')
        constraints.add(blocknumber == 0)

        timestamp = constraints.new_bitvec(256, name='timestamp')
        constraints.add(timestamp == 1)

        difficulty = constraints.new_bitvec(256, name='difficulty')
        constraints.add(difficulty == 256)

        coinbase = constraints.new_bitvec(256, name='coinbase')
        constraints.add(coinbase == 244687034288125203496486448490407391986876152250)

        gaslimit = constraints.new_bitvec(256, name='gaslimit')
        constraints.add(gaslimit == 1000000)

        world = evm.EVMWorld(constraints, blocknumber=blocknumber, timestamp=timestamp, difficulty=difficulty,
                             coinbase=coinbase, gaslimit=gaslimit)
    
        acc_addr = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        acc_code = unhexlify('7faabbffffffffffffffffffffffffffffffffffffffffffffffffffffffffccdd600052600060006000600060016000a4')
            
        acc_balance = constraints.new_bitvec(256, name='balance_0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6')
        constraints.add(acc_balance == 100000000000000000000000)

        acc_nonce = constraints.new_bitvec(256, name='nonce_0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6')
        constraints.add(acc_nonce == 0)

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        caller = 0xcd1722f3947def4cf144679da39c4c32bdc35681
        price = constraints.new_bitvec(256, name='price')
        constraints.add(price == 100000000000000)

        value = constraints.new_bitvec(256, name='value')
        constraints.add(value == 1000000000000000000)

        gas = constraints.new_bitvec(256, name='gas')
        constraints.add(gas == 100000)

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
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('7faabbffffffffffffffffffffffffffffffffffffffffffffffffffffffffccdd600052600060006000600060016000a4'))
        # check outs
        self.assertEqual(returndata, unhexlify(''))
        # check logs
        logs = [Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs]
        data = rlp.encode(logs)
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '23be46fc7a6c306a308a3f05719e0b0e5f9009a10f54838a78afa750b1ef17d7')

        # test used gas
        self.assertEqual(solve(world.current_vm.gas), 98087)

    def test_log2_nonEmptyMem(self):
        """
        Textcase taken from https://github.com/ethereum/tests
        File: log2_nonEmptyMem.json
        sha256sum: d25456c1c7820ede2370ffde1b59ae243c88f11554087f01ce8b55a2a1988c7c
        Code:     PUSH32 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
                  PUSH1 0x0
                  MSTORE
                  PUSH1 0x0
                  PUSH1 0x0
                  PUSH1 0x20
                  PUSH1 0x0
                  LOG2
        """    
    
        solver = Z3Solver()

        def solve(val):
            results = solver.get_all_values(constraints, val)
            # We constrain all values to single values!
            self.assertEqual(len(results), 1)
            return results[0]

        constraints = ConstraintSet()

        blocknumber = constraints.new_bitvec(256, name='blocknumber')
        constraints.add(blocknumber == 0)

        timestamp = constraints.new_bitvec(256, name='timestamp')
        constraints.add(timestamp == 1)

        difficulty = constraints.new_bitvec(256, name='difficulty')
        constraints.add(difficulty == 256)

        coinbase = constraints.new_bitvec(256, name='coinbase')
        constraints.add(coinbase == 244687034288125203496486448490407391986876152250)

        gaslimit = constraints.new_bitvec(256, name='gaslimit')
        constraints.add(gaslimit == 1000000)

        world = evm.EVMWorld(constraints, blocknumber=blocknumber, timestamp=timestamp, difficulty=difficulty,
                             coinbase=coinbase, gaslimit=gaslimit)
    
        acc_addr = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        acc_code = unhexlify('7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff6000526000600060206000a2')
            
        acc_balance = constraints.new_bitvec(256, name='balance_0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6')
        constraints.add(acc_balance == 100000000000000000000000)

        acc_nonce = constraints.new_bitvec(256, name='nonce_0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6')
        constraints.add(acc_nonce == 0)

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        caller = 0xcd1722f3947def4cf144679da39c4c32bdc35681
        price = constraints.new_bitvec(256, name='price')
        constraints.add(price == 100000000000000)

        value = constraints.new_bitvec(256, name='value')
        constraints.add(value == 1000000000000000000)

        gas = constraints.new_bitvec(256, name='gas')
        constraints.add(gas == 100000)

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
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff6000526000600060206000a2'))
        # check outs
        self.assertEqual(returndata, unhexlify(''))
        # check logs
        logs = [Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs]
        data = rlp.encode(logs)
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '6e02fdc5f0bf3152415cc76a6ed19cd23f9eee9c8ada826de72bfab8c0bbb103')

        # test used gas
        self.assertEqual(solve(world.current_vm.gas), 98595)

    def test_log4_PC(self):
        """
        Textcase taken from https://github.com/ethereum/tests
        File: log4_PC.json
        sha256sum: 2c7035c93b4d925802f6057c1fbdf59e40a753d8c02034531b589ac6e7b15b5d
        Code:     PUSH1 0xff
                  PUSH1 0x0
                  MSTORE8
                  GETPC
                  GETPC
                  GETPC
                  GETPC
                  PUSH1 0x20
                  PUSH1 0x0
                  LOG4
        """    
    
        solver = Z3Solver()

        def solve(val):
            results = solver.get_all_values(constraints, val)
            # We constrain all values to single values!
            self.assertEqual(len(results), 1)
            return results[0]

        constraints = ConstraintSet()

        blocknumber = constraints.new_bitvec(256, name='blocknumber')
        constraints.add(blocknumber == 0)

        timestamp = constraints.new_bitvec(256, name='timestamp')
        constraints.add(timestamp == 1)

        difficulty = constraints.new_bitvec(256, name='difficulty')
        constraints.add(difficulty == 256)

        coinbase = constraints.new_bitvec(256, name='coinbase')
        constraints.add(coinbase == 244687034288125203496486448490407391986876152250)

        gaslimit = constraints.new_bitvec(256, name='gaslimit')
        constraints.add(gaslimit == 1000000)

        world = evm.EVMWorld(constraints, blocknumber=blocknumber, timestamp=timestamp, difficulty=difficulty,
                             coinbase=coinbase, gaslimit=gaslimit)
    
        acc_addr = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        acc_code = unhexlify('60ff6000535858585860206000a4')
            
        acc_balance = constraints.new_bitvec(256, name='balance_0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6')
        constraints.add(acc_balance == 100000000000000000000000)

        acc_nonce = constraints.new_bitvec(256, name='nonce_0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6')
        constraints.add(acc_nonce == 0)

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        caller = 0xcd1722f3947def4cf144679da39c4c32bdc35681
        price = constraints.new_bitvec(256, name='price')
        constraints.add(price == 100000000000000)

        value = constraints.new_bitvec(256, name='value')
        constraints.add(value == 1000000000000000000)

        gas = constraints.new_bitvec(256, name='gas')
        constraints.add(gas == 100000)

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
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('60ff6000535858585860206000a4'))
        # check outs
        self.assertEqual(returndata, unhexlify(''))
        # check logs
        logs = [Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs]
        data = rlp.encode(logs)
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '51d56b9f9e0edb35517910cf8ed0e7a6b83aad7c2ca5c9b23874294aa0fae264')

        # test used gas
        self.assertEqual(solve(world.current_vm.gas), 97843)

    def test_log4_emptyMem(self):
        """
        Textcase taken from https://github.com/ethereum/tests
        File: log4_emptyMem.json
        sha256sum: bc7cac7219881575c8e043a83d13985f6f7160a86d87bf742ea8f427862516d3
        Code:     PUSH1 0x0
                  PUSH1 0x0
                  PUSH1 0x0
                  PUSH1 0x0
                  PUSH1 0x0
                  PUSH1 0x0
                  LOG4
        """    
    
        solver = Z3Solver()

        def solve(val):
            results = solver.get_all_values(constraints, val)
            # We constrain all values to single values!
            self.assertEqual(len(results), 1)
            return results[0]

        constraints = ConstraintSet()

        blocknumber = constraints.new_bitvec(256, name='blocknumber')
        constraints.add(blocknumber == 0)

        timestamp = constraints.new_bitvec(256, name='timestamp')
        constraints.add(timestamp == 1)

        difficulty = constraints.new_bitvec(256, name='difficulty')
        constraints.add(difficulty == 256)

        coinbase = constraints.new_bitvec(256, name='coinbase')
        constraints.add(coinbase == 244687034288125203496486448490407391986876152250)

        gaslimit = constraints.new_bitvec(256, name='gaslimit')
        constraints.add(gaslimit == 1000000)

        world = evm.EVMWorld(constraints, blocknumber=blocknumber, timestamp=timestamp, difficulty=difficulty,
                             coinbase=coinbase, gaslimit=gaslimit)
    
        acc_addr = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        acc_code = unhexlify('600060006000600060006000a4')
            
        acc_balance = constraints.new_bitvec(256, name='balance_0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6')
        constraints.add(acc_balance == 100000000000000000000000)

        acc_nonce = constraints.new_bitvec(256, name='nonce_0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6')
        constraints.add(acc_nonce == 0)

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        caller = 0xcd1722f3947def4cf144679da39c4c32bdc35681
        price = constraints.new_bitvec(256, name='price')
        constraints.add(price == 100000000000000)

        value = constraints.new_bitvec(256, name='value')
        constraints.add(value == 1000000000000000000)

        gas = constraints.new_bitvec(256, name='gas')
        constraints.add(gas == 100000)

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
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('600060006000600060006000a4'))
        # check outs
        self.assertEqual(returndata, unhexlify(''))
        # check logs
        logs = [Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs]
        data = rlp.encode(logs)
        self.assertEqual(sha3.keccak_256(data).hexdigest(), 'c04befec57a9284dbf7636641a59a938acf437ae400154e34ad0a1cfeee3eaa9')

        # test used gas
        self.assertEqual(solve(world.current_vm.gas), 98107)

    def test_log0_nonEmptyMem_logMemSize1_logMemStart31(self):
        """
        Textcase taken from https://github.com/ethereum/tests
        File: log0_nonEmptyMem_logMemSize1_logMemStart31.json
        sha256sum: 1261f42204f5cc01c05e376e5c5cc1c7904ee7a75fc185b3155b8d8348aacc31
        Code:     PUSH32 0xaabbffffffffffffffffffffffffffffffffffffffffffffffffffffffffccdd
                  PUSH1 0x0
                  MSTORE
                  PUSH1 0x1
                  PUSH1 0x1f
                  LOG0
        """    
    
        solver = Z3Solver()

        def solve(val):
            results = solver.get_all_values(constraints, val)
            # We constrain all values to single values!
            self.assertEqual(len(results), 1)
            return results[0]

        constraints = ConstraintSet()

        blocknumber = constraints.new_bitvec(256, name='blocknumber')
        constraints.add(blocknumber == 0)

        timestamp = constraints.new_bitvec(256, name='timestamp')
        constraints.add(timestamp == 1)

        difficulty = constraints.new_bitvec(256, name='difficulty')
        constraints.add(difficulty == 256)

        coinbase = constraints.new_bitvec(256, name='coinbase')
        constraints.add(coinbase == 244687034288125203496486448490407391986876152250)

        gaslimit = constraints.new_bitvec(256, name='gaslimit')
        constraints.add(gaslimit == 1000000)

        world = evm.EVMWorld(constraints, blocknumber=blocknumber, timestamp=timestamp, difficulty=difficulty,
                             coinbase=coinbase, gaslimit=gaslimit)
    
        acc_addr = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        acc_code = unhexlify('7faabbffffffffffffffffffffffffffffffffffffffffffffffffffffffffccdd6000526001601fa0')
            
        acc_balance = constraints.new_bitvec(256, name='balance_0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6')
        constraints.add(acc_balance == 100000000000000000000000)

        acc_nonce = constraints.new_bitvec(256, name='nonce_0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6')
        constraints.add(acc_nonce == 0)

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        caller = 0xcd1722f3947def4cf144679da39c4c32bdc35681
        price = constraints.new_bitvec(256, name='price')
        constraints.add(price == 100000000000000)

        value = constraints.new_bitvec(256, name='value')
        constraints.add(value == 1000000000000000000)

        gas = constraints.new_bitvec(256, name='gas')
        constraints.add(gas == 100000)

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
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('7faabbffffffffffffffffffffffffffffffffffffffffffffffffffffffffccdd6000526001601fa0'))
        # check outs
        self.assertEqual(returndata, unhexlify(''))
        # check logs
        logs = [Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs]
        data = rlp.encode(logs)
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '6db1ea69b7b1f555653d63d1aea297db1b4997dc26ba1d97e724aae34278a459')

        # test used gas
        self.assertEqual(solve(world.current_vm.gas), 99599)

    def test_log0_logMemStartTooHigh(self):
        """
        Textcase taken from https://github.com/ethereum/tests
        File: log0_logMemStartTooHigh.json
        sha256sum: a1ddd4d5bcc123bc356bd74a6db495a3c7265e56bb0df278b32f30b2f338f74d
        Code:     PUSH32 0xaabbffffffffffffffffffffffffffffffffffffffffffffffffffffffffccdd
                  PUSH1 0x0
                  MSTORE
                  PUSH1 0x1
                  PUSH32 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
                  LOG0
        """    
    
        solver = Z3Solver()

        def solve(val):
            results = solver.get_all_values(constraints, val)
            # We constrain all values to single values!
            self.assertEqual(len(results), 1)
            return results[0]

        constraints = ConstraintSet()

        blocknumber = constraints.new_bitvec(256, name='blocknumber')
        constraints.add(blocknumber == 0)

        timestamp = constraints.new_bitvec(256, name='timestamp')
        constraints.add(timestamp == 1)

        difficulty = constraints.new_bitvec(256, name='difficulty')
        constraints.add(difficulty == 256)

        coinbase = constraints.new_bitvec(256, name='coinbase')
        constraints.add(coinbase == 244687034288125203496486448490407391986876152250)

        gaslimit = constraints.new_bitvec(256, name='gaslimit')
        constraints.add(gaslimit == 1000000)

        world = evm.EVMWorld(constraints, blocknumber=blocknumber, timestamp=timestamp, difficulty=difficulty,
                             coinbase=coinbase, gaslimit=gaslimit)
    
        acc_addr = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        acc_code = unhexlify('7faabbffffffffffffffffffffffffffffffffffffffffffffffffffffffffccdd60005260017fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffa0')
            
        acc_balance = constraints.new_bitvec(256, name='balance_0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6')
        constraints.add(acc_balance == 100000000000000000000000)

        acc_nonce = constraints.new_bitvec(256, name='nonce_0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6')
        constraints.add(acc_nonce == 0)

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        caller = 0xcd1722f3947def4cf144679da39c4c32bdc35681
        price = constraints.new_bitvec(256, name='price')
        constraints.add(price == 100000000000000)

        value = constraints.new_bitvec(256, name='value')
        constraints.add(value == 1000000000000000000)

        gas = constraints.new_bitvec(256, name='gas')
        constraints.add(gas == 100000)

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

        # If test end in exception check it here
        self.assertTrue(result == 'THROW')

    def test_log0_emptyMem(self):
        """
        Textcase taken from https://github.com/ethereum/tests
        File: log0_emptyMem.json
        sha256sum: 0d93034612b2fe1bcda64d8f748adc6c3627c81d07f58694184f875c000de180
        Code:     PUSH1 0x0
                  PUSH1 0x0
                  LOG0
        """    
    
        solver = Z3Solver()

        def solve(val):
            results = solver.get_all_values(constraints, val)
            # We constrain all values to single values!
            self.assertEqual(len(results), 1)
            return results[0]

        constraints = ConstraintSet()

        blocknumber = constraints.new_bitvec(256, name='blocknumber')
        constraints.add(blocknumber == 0)

        timestamp = constraints.new_bitvec(256, name='timestamp')
        constraints.add(timestamp == 1)

        difficulty = constraints.new_bitvec(256, name='difficulty')
        constraints.add(difficulty == 256)

        coinbase = constraints.new_bitvec(256, name='coinbase')
        constraints.add(coinbase == 244687034288125203496486448490407391986876152250)

        gaslimit = constraints.new_bitvec(256, name='gaslimit')
        constraints.add(gaslimit == 1000000)

        world = evm.EVMWorld(constraints, blocknumber=blocknumber, timestamp=timestamp, difficulty=difficulty,
                             coinbase=coinbase, gaslimit=gaslimit)
    
        acc_addr = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        acc_code = unhexlify('60006000a0')
            
        acc_balance = constraints.new_bitvec(256, name='balance_0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6')
        constraints.add(acc_balance == 100000000000000000000000)

        acc_nonce = constraints.new_bitvec(256, name='nonce_0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6')
        constraints.add(acc_nonce == 0)

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        caller = 0xcd1722f3947def4cf144679da39c4c32bdc35681
        price = constraints.new_bitvec(256, name='price')
        constraints.add(price == 100000000000000)

        value = constraints.new_bitvec(256, name='value')
        constraints.add(value == 1000000000000000000)

        gas = constraints.new_bitvec(256, name='gas')
        constraints.add(gas == 100000)

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
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('60006000a0'))
        # check outs
        self.assertEqual(returndata, unhexlify(''))
        # check logs
        logs = [Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs]
        data = rlp.encode(logs)
        self.assertEqual(sha3.keccak_256(data).hexdigest(), 'ea63b4dbbdbca1bd985580a0c3b6f35a4955d4d4cf0b4d903003cdfc4c40ba1c')

        # test used gas
        self.assertEqual(solve(world.current_vm.gas), 99619)


if __name__ == '__main__':
    unittest.main()
