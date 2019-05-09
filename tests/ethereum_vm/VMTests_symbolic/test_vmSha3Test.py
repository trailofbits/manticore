"""DO NOT MODIFY: Tests generated from `VMTests/vmSha3Test` with make_VMTests.py"""
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


class Log(rlp.Serializable):
    fields = [
        ('address', Binary.fixed_length(20, allow_empty=True)),
        ('topics', CountableList(BigEndianInt(32))),
        ('data', Binary())
    ]


class EVMTest_vmSha3Test(unittest.TestCase):
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

    def test_sha3_bigOffset(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: sha3_bigOffset.json
        sha256sum: d381e3c19ddeceb5d17b00878dc48a9c4c89de423f4afd14cc0bf5887bf926e9
        Code:     PUSH1 0x2
                  PUSH31 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
                  SHA3
                  PUSH1 0x0
                  SSTORE
        """    
    
        def solve(val):
            results = Z3Solver.instance().get_all_values(constraints, val)
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
        acc_code = unhexlify('60027e0fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff20600055')
            
        acc_balance = constraints.new_bitvec(256, name='balance_0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6')
        constraints.add(acc_balance == 115792089237316195423570985008687907853269984665640564039457584007913129639935)

        acc_nonce = constraints.new_bitvec(256, name='nonce_0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6')
        constraints.add(acc_nonce == 0)

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        caller = 0xcd1722f3947def4cf144679da39c4c32bdc35681
        price = constraints.new_bitvec(256, name='price')
        constraints.add(price == 1)

        value = constraints.new_bitvec(256, name='value')
        constraints.add(value == 115792089237316195423570985008687907853269984665640564039457584007913129639935)

        gas = constraints.new_bitvec(256, name='gas')
        constraints.add(gas == 1099511627776)

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
        self.assertEqual(solve(world.block_coinbase()), 0x2adc25665018aa1fe0e6bc666dac8fc2697ff9ba)

        # If test end in exception check it here
        self.assertTrue(result == 'THROW')

    def test_sha3_1(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: sha3_1.json
        sha256sum: 06ec9a0bcd254538de14028e6546a5b2db030314e8d94f05449bb7d5d5d01bcf
        Code:     PUSH1 0x5
                  PUSH1 0x4
                  SHA3
                  PUSH1 0x0
                  SSTORE
        """    
    
        def solve(val):
            results = Z3Solver.instance().get_all_values(constraints, val)
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
        acc_code = unhexlify('6005600420600055')
            
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
        self.assertEqual(solve(world.block_coinbase()), 0x2adc25665018aa1fe0e6bc666dac8fc2697ff9ba)

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 0)
        self.assertEqual(solve(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 100000000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('6005600420600055'))
        # check storage
        self.assertEqual(solve(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0xc41589e7559804ea4a2080dad19d876a024ccb05117835447d72ce08c1d020ec)
        # check outs
        self.assertEqual(returndata, unhexlify(''))
        # check logs
        logs = [Log(unhexlify('{:040x}'.format(l.address)), l.topics, solve(l.memlog)) for l in world.logs]
        data = rlp.encode(logs)
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')

        # test used gas
        self.assertEqual(solve(world.current_vm.gas), 79952)

    def test_sha3_memSizeQuadraticCost63(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: sha3_memSizeQuadraticCost63.json
        sha256sum: be4410faf392a488302eaf658415d8c6daa0a2ba509385284eb4c0ec824ee2a7
        Code:     PUSH1 0x1
                  PUSH2 0x7c0
                  SHA3
                  PUSH1 0x0
                  SSTORE
        """    
    
        def solve(val):
            results = Z3Solver.instance().get_all_values(constraints, val)
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
        acc_code = unhexlify('60016107c020600055')
            
        acc_balance = constraints.new_bitvec(256, name='balance_0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6')
        constraints.add(acc_balance == 115792089237316195423570985008687907853269984665640564039457584007913129639935)

        acc_nonce = constraints.new_bitvec(256, name='nonce_0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6')
        constraints.add(acc_nonce == 0)

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        caller = 0xcd1722f3947def4cf144679da39c4c32bdc35681
        price = constraints.new_bitvec(256, name='price')
        constraints.add(price == 1)

        value = constraints.new_bitvec(256, name='value')
        constraints.add(value == 115792089237316195423570985008687907853269984665640564039457584007913129639935)

        gas = constraints.new_bitvec(256, name='gas')
        constraints.add(gas == 4294967296)

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
        self.assertEqual(solve(world.block_coinbase()), 0x2adc25665018aa1fe0e6bc666dac8fc2697ff9ba)

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 0)
        self.assertEqual(solve(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 115792089237316195423570985008687907853269984665640564039457584007913129639935)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('60016107c020600055'))
        # check storage
        self.assertEqual(solve(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0xbc36789e7a1e281436464229828f817d6612f7b477d66591ff96a9e064bcc98a)
        # check outs
        self.assertEqual(returndata, unhexlify(''))
        # check logs
        logs = [Log(unhexlify('{:040x}'.format(l.address)), l.topics, solve(l.memlog)) for l in world.logs]
        data = rlp.encode(logs)
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')

        # test used gas
        self.assertEqual(solve(world.current_vm.gas), 4294947055)

    def test_sha3_0(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: sha3_0.json
        sha256sum: b16c2447ed93b44a839c27b5aa69cd9d1af5e6eeb93680e9d04e79c48bf25cb5
        Code:     PUSH1 0x0
                  PUSH1 0x0
                  SHA3
                  PUSH1 0x0
                  SSTORE
        """    
    
        def solve(val):
            results = Z3Solver.instance().get_all_values(constraints, val)
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
        acc_code = unhexlify('6000600020600055')
            
        acc_balance = constraints.new_bitvec(256, name='balance_0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6')
        constraints.add(acc_balance == 100000000000000000000000)

        acc_nonce = constraints.new_bitvec(256, name='nonce_0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6')
        constraints.add(acc_nonce == 0)

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        caller = 0xcd1722f3947def4cf144679da39c4c32bdc35681
        price = constraints.new_bitvec(256, name='price')
        constraints.add(price == 1000000000)

        value = constraints.new_bitvec(256, name='value')
        constraints.add(value == 1000000000000000000)

        gas = constraints.new_bitvec(256, name='gas')
        constraints.add(gas == 100000000000)

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
        self.assertEqual(solve(world.block_coinbase()), 0x2adc25665018aa1fe0e6bc666dac8fc2697ff9ba)

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 0)
        self.assertEqual(solve(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 100000000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('6000600020600055'))
        # check storage
        self.assertEqual(solve(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0xc5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470)
        # check outs
        self.assertEqual(returndata, unhexlify(''))
        # check logs
        logs = [Log(unhexlify('{:040x}'.format(l.address)), l.topics, solve(l.memlog)) for l in world.logs]
        data = rlp.encode(logs)
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')

        # test used gas
        self.assertEqual(solve(world.current_vm.gas), 99999979961)

    def test_sha3_bigOffset2(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: sha3_bigOffset2.json
        sha256sum: 1c9f5059c6713f7565b7bfab1e14f2ad51ecc3bf19b1f977e8a4e9b0e9717e73
        Code:     PUSH1 0x2
                  PUSH4 0x1000000
                  SHA3
                  PUSH1 0x0
                  SSTORE
        """    
    
        def solve(val):
            results = Z3Solver.instance().get_all_values(constraints, val)
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
        acc_code = unhexlify('6002630100000020600055')
            
        acc_balance = constraints.new_bitvec(256, name='balance_0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6')
        constraints.add(acc_balance == 115792089237316195423570985008687907853269984665640564039457584007913129639935)

        acc_nonce = constraints.new_bitvec(256, name='nonce_0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6')
        constraints.add(acc_nonce == 0)

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        caller = 0xcd1722f3947def4cf144679da39c4c32bdc35681
        price = constraints.new_bitvec(256, name='price')
        constraints.add(price == 1)

        value = constraints.new_bitvec(256, name='value')
        constraints.add(value == 115792089237316195423570985008687907853269984665640564039457584007913129639935)

        gas = constraints.new_bitvec(256, name='gas')
        constraints.add(gas == 4294967296)

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
        self.assertEqual(solve(world.block_coinbase()), 0x2adc25665018aa1fe0e6bc666dac8fc2697ff9ba)

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 0)
        self.assertEqual(solve(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 115792089237316195423570985008687907853269984665640564039457584007913129639935)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('6002630100000020600055'))
        # check storage
        self.assertEqual(solve(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0x54a8c0ab653c15bfb48b47fd011ba2b9617af01cb45cab344acd57c924d56798)
        # check outs
        self.assertEqual(returndata, unhexlify(''))
        # check logs
        logs = [Log(unhexlify('{:040x}'.format(l.address)), l.topics, solve(l.memlog)) for l in world.logs]
        data = rlp.encode(logs)
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')

        # test used gas
        self.assertEqual(solve(world.current_vm.gas), 3756501424)

    def test_sha3_5(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: sha3_5.json
        sha256sum: f1b06ddff755484ae7e36328eeed833792d5e77233e453b0d348e8c1ffbfd41d
        Code:     PUSH5 0xfffffffff
                  PUSH2 0x2710
                  SHA3
                  PUSH1 0x0
                  SSTORE
        """    
    
        def solve(val):
            results = Z3Solver.instance().get_all_values(constraints, val)
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
        acc_code = unhexlify('640fffffffff61271020600055')
            
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
        self.assertEqual(solve(world.block_coinbase()), 0x2adc25665018aa1fe0e6bc666dac8fc2697ff9ba)

        # If test end in exception check it here
        self.assertTrue(result == 'THROW')

    def test_sha3_6(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: sha3_6.json
        sha256sum: f5ee9409dda75eee4e96bb3e2a76a3d74f1650f0fe5efc60d4dbb369ce252a08
        Code:     PUSH32 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
                  PUSH32 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
                  SHA3
                  PUSH1 0x0
                  SSTORE
        """    
    
        def solve(val):
            results = Z3Solver.instance().get_all_values(constraints, val)
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
        acc_code = unhexlify('7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff20600055')
            
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
        self.assertEqual(solve(world.block_coinbase()), 0x2adc25665018aa1fe0e6bc666dac8fc2697ff9ba)

        # If test end in exception check it here
        self.assertTrue(result == 'THROW')

    def test_sha3_memSizeNoQuadraticCost31(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: sha3_memSizeNoQuadraticCost31.json
        sha256sum: fc2ba6b1f8589077e45bdbaca4d5130c458598a413c6ecf2df617aaf6f9e11b1
        Code:     PUSH1 0x1
                  PUSH2 0x3c0
                  SHA3
                  PUSH1 0x0
                  SSTORE
        """    
    
        def solve(val):
            results = Z3Solver.instance().get_all_values(constraints, val)
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
        acc_code = unhexlify('60016103c020600055')
            
        acc_balance = constraints.new_bitvec(256, name='balance_0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6')
        constraints.add(acc_balance == 115792089237316195423570985008687907853269984665640564039457584007913129639935)

        acc_nonce = constraints.new_bitvec(256, name='nonce_0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6')
        constraints.add(acc_nonce == 0)

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        caller = 0xcd1722f3947def4cf144679da39c4c32bdc35681
        price = constraints.new_bitvec(256, name='price')
        constraints.add(price == 1)

        value = constraints.new_bitvec(256, name='value')
        constraints.add(value == 115792089237316195423570985008687907853269984665640564039457584007913129639935)

        gas = constraints.new_bitvec(256, name='gas')
        constraints.add(gas == 4294967296)

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
        self.assertEqual(solve(world.block_coinbase()), 0x2adc25665018aa1fe0e6bc666dac8fc2697ff9ba)

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 0)
        self.assertEqual(solve(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 115792089237316195423570985008687907853269984665640564039457584007913129639935)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('60016103c020600055'))
        # check storage
        self.assertEqual(solve(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0xbc36789e7a1e281436464229828f817d6612f7b477d66591ff96a9e064bcc98a)
        # check outs
        self.assertEqual(returndata, unhexlify(''))
        # check logs
        logs = [Log(unhexlify('{:040x}'.format(l.address)), l.topics, solve(l.memlog)) for l in world.logs]
        data = rlp.encode(logs)
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')

        # test used gas
        self.assertEqual(solve(world.current_vm.gas), 4294947157)

    def test_sha3_3(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: sha3_3.json
        sha256sum: 717cdaf13fe74709e05442ff2689169fae1d272b0fb7a5e48a6f4d564dd9a64c
        Code:     PUSH3 0xfffff
                  PUSH2 0x3e8
                  SHA3
                  PUSH1 0x0
                  SSTORE
        """    
    
        def solve(val):
            results = Z3Solver.instance().get_all_values(constraints, val)
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
        acc_code = unhexlify('620fffff6103e820600055')
            
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
        self.assertEqual(solve(world.block_coinbase()), 0x2adc25665018aa1fe0e6bc666dac8fc2697ff9ba)

        # If test end in exception check it here
        self.assertTrue(result == 'THROW')

    def test_sha3_memSizeQuadraticCost33(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: sha3_memSizeQuadraticCost33.json
        sha256sum: ad3ad47d84ee8dddaa8ee616f1015c7e094e1e3823ea7c0876011cfc4101fb00
        Code:     PUSH1 0x1
                  PUSH2 0x400
                  SHA3
                  PUSH1 0x0
                  SSTORE
        """    
    
        def solve(val):
            results = Z3Solver.instance().get_all_values(constraints, val)
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
        acc_code = unhexlify('600161040020600055')
            
        acc_balance = constraints.new_bitvec(256, name='balance_0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6')
        constraints.add(acc_balance == 115792089237316195423570985008687907853269984665640564039457584007913129639935)

        acc_nonce = constraints.new_bitvec(256, name='nonce_0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6')
        constraints.add(acc_nonce == 0)

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        caller = 0xcd1722f3947def4cf144679da39c4c32bdc35681
        price = constraints.new_bitvec(256, name='price')
        constraints.add(price == 1)

        value = constraints.new_bitvec(256, name='value')
        constraints.add(value == 115792089237316195423570985008687907853269984665640564039457584007913129639935)

        gas = constraints.new_bitvec(256, name='gas')
        constraints.add(gas == 4294967296)

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
        self.assertEqual(solve(world.block_coinbase()), 0x2adc25665018aa1fe0e6bc666dac8fc2697ff9ba)

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 0)
        self.assertEqual(solve(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 115792089237316195423570985008687907853269984665640564039457584007913129639935)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('600161040020600055'))
        # check storage
        self.assertEqual(solve(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0xbc36789e7a1e281436464229828f817d6612f7b477d66591ff96a9e064bcc98a)
        # check outs
        self.assertEqual(returndata, unhexlify(''))
        # check logs
        logs = [Log(unhexlify('{:040x}'.format(l.address)), l.topics, solve(l.memlog)) for l in world.logs]
        data = rlp.encode(logs)
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')

        # test used gas
        self.assertEqual(solve(world.current_vm.gas), 4294947150)

    def test_sha3_memSizeQuadraticCost64_2(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: sha3_memSizeQuadraticCost64_2.json
        sha256sum: 7f8135486f7f54eddee88c3bfb21d072a58916698b436901dbe04cbe7835892c
        Code:     PUSH1 0x20
                  PUSH2 0x7e0
                  SHA3
                  PUSH1 0x0
                  SSTORE
        """    
    
        def solve(val):
            results = Z3Solver.instance().get_all_values(constraints, val)
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
        acc_code = unhexlify('60206107e020600055')
            
        acc_balance = constraints.new_bitvec(256, name='balance_0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6')
        constraints.add(acc_balance == 115792089237316195423570985008687907853269984665640564039457584007913129639935)

        acc_nonce = constraints.new_bitvec(256, name='nonce_0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6')
        constraints.add(acc_nonce == 0)

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        caller = 0xcd1722f3947def4cf144679da39c4c32bdc35681
        price = constraints.new_bitvec(256, name='price')
        constraints.add(price == 1)

        value = constraints.new_bitvec(256, name='value')
        constraints.add(value == 115792089237316195423570985008687907853269984665640564039457584007913129639935)

        gas = constraints.new_bitvec(256, name='gas')
        constraints.add(gas == 4294967296)

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
        self.assertEqual(solve(world.block_coinbase()), 0x2adc25665018aa1fe0e6bc666dac8fc2697ff9ba)

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 0)
        self.assertEqual(solve(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 115792089237316195423570985008687907853269984665640564039457584007913129639935)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('60206107e020600055'))
        # check storage
        self.assertEqual(solve(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0x290decd9548b62a8d60345a988386fc84ba6bc95484008f6362f93160ef3e563)
        # check outs
        self.assertEqual(returndata, unhexlify(''))
        # check logs
        logs = [Log(unhexlify('{:040x}'.format(l.address)), l.topics, solve(l.memlog)) for l in world.logs]
        data = rlp.encode(logs)
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')

        # test used gas
        self.assertEqual(solve(world.current_vm.gas), 4294947051)

    def test_sha3_2(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: sha3_2.json
        sha256sum: 16e818c59b447c116dc5ba02ed573b26eab288f98d81c231b20972089ccdbf7b
        Code:     PUSH1 0xa
                  PUSH1 0xa
                  SHA3
                  PUSH1 0x0
                  SSTORE
        """    
    
        def solve(val):
            results = Z3Solver.instance().get_all_values(constraints, val)
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
        acc_code = unhexlify('600a600a20600055')
            
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
        self.assertEqual(solve(world.block_coinbase()), 0x2adc25665018aa1fe0e6bc666dac8fc2697ff9ba)

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 0)
        self.assertEqual(solve(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 100000000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('600a600a20600055'))
        # check storage
        self.assertEqual(solve(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0x6bd2dd6bd408cbee33429358bf24fdc64612fbf8b1b4db604518f40ffd34b607)
        # check outs
        self.assertEqual(returndata, unhexlify(''))
        # check logs
        logs = [Log(unhexlify('{:040x}'.format(l.address)), l.topics, solve(l.memlog)) for l in world.logs]
        data = rlp.encode(logs)
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')

        # test used gas
        self.assertEqual(solve(world.current_vm.gas), 79952)

    def test_sha3_memSizeQuadraticCost32_zeroSize(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: sha3_memSizeQuadraticCost32_zeroSize.json
        sha256sum: 4c0510b87646542f19de5f4f8329db95d5342d5b42c8de02577c8a2b94145e9c
        Code:     PUSH1 0x0
                  PUSH2 0x400
                  SHA3
                  PUSH1 0x0
                  SSTORE
        """    
    
        def solve(val):
            results = Z3Solver.instance().get_all_values(constraints, val)
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
        acc_code = unhexlify('600061040020600055')
            
        acc_balance = constraints.new_bitvec(256, name='balance_0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6')
        constraints.add(acc_balance == 115792089237316195423570985008687907853269984665640564039457584007913129639935)

        acc_nonce = constraints.new_bitvec(256, name='nonce_0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6')
        constraints.add(acc_nonce == 0)

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        caller = 0xcd1722f3947def4cf144679da39c4c32bdc35681
        price = constraints.new_bitvec(256, name='price')
        constraints.add(price == 1)

        value = constraints.new_bitvec(256, name='value')
        constraints.add(value == 115792089237316195423570985008687907853269984665640564039457584007913129639935)

        gas = constraints.new_bitvec(256, name='gas')
        constraints.add(gas == 4294967296)

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
        self.assertEqual(solve(world.block_coinbase()), 0x2adc25665018aa1fe0e6bc666dac8fc2697ff9ba)

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 0)
        self.assertEqual(solve(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 115792089237316195423570985008687907853269984665640564039457584007913129639935)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('600061040020600055'))
        # check storage
        self.assertEqual(solve(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0xc5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470)
        # check outs
        self.assertEqual(returndata, unhexlify(''))
        # check logs
        logs = [Log(unhexlify('{:040x}'.format(l.address)), l.topics, solve(l.memlog)) for l in world.logs]
        data = rlp.encode(logs)
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')

        # test used gas
        self.assertEqual(solve(world.current_vm.gas), 4294947257)

    def test_sha3_memSizeQuadraticCost65(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: sha3_memSizeQuadraticCost65.json
        sha256sum: 616fcdfca3307703efa81630eae1ba039b88dd836931599ea0e416c6ccf1ecac
        Code:     PUSH1 0x1
                  PUSH2 0x800
                  SHA3
                  PUSH1 0x0
                  SSTORE
        """    
    
        def solve(val):
            results = Z3Solver.instance().get_all_values(constraints, val)
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
        acc_code = unhexlify('600161080020600055')
            
        acc_balance = constraints.new_bitvec(256, name='balance_0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6')
        constraints.add(acc_balance == 115792089237316195423570985008687907853269984665640564039457584007913129639935)

        acc_nonce = constraints.new_bitvec(256, name='nonce_0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6')
        constraints.add(acc_nonce == 0)

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        caller = 0xcd1722f3947def4cf144679da39c4c32bdc35681
        price = constraints.new_bitvec(256, name='price')
        constraints.add(price == 1)

        value = constraints.new_bitvec(256, name='value')
        constraints.add(value == 115792089237316195423570985008687907853269984665640564039457584007913129639935)

        gas = constraints.new_bitvec(256, name='gas')
        constraints.add(gas == 4294967296)

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
        self.assertEqual(solve(world.block_coinbase()), 0x2adc25665018aa1fe0e6bc666dac8fc2697ff9ba)

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 0)
        self.assertEqual(solve(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 115792089237316195423570985008687907853269984665640564039457584007913129639935)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('600161080020600055'))
        # check storage
        self.assertEqual(solve(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0xbc36789e7a1e281436464229828f817d6612f7b477d66591ff96a9e064bcc98a)
        # check outs
        self.assertEqual(returndata, unhexlify(''))
        # check logs
        logs = [Log(unhexlify('{:040x}'.format(l.address)), l.topics, solve(l.memlog)) for l in world.logs]
        data = rlp.encode(logs)
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')

        # test used gas
        self.assertEqual(solve(world.current_vm.gas), 4294947048)

    def test_sha3_4(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: sha3_4.json
        sha256sum: e9819eab0f7768ce9b44b06274a98109c4f8d9a1ad7b99b73ec02e77d0813a4c
        Code:     PUSH1 0x64
                  PUSH5 0xfffffffff
                  SHA3
                  PUSH1 0x0
                  SSTORE
        """    
    
        def solve(val):
            results = Z3Solver.instance().get_all_values(constraints, val)
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
        acc_code = unhexlify('6064640fffffffff20600055')
            
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
        self.assertEqual(solve(world.block_coinbase()), 0x2adc25665018aa1fe0e6bc666dac8fc2697ff9ba)

        # If test end in exception check it here
        self.assertTrue(result == 'THROW')

    def test_sha3_memSizeQuadraticCost32(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: sha3_memSizeQuadraticCost32.json
        sha256sum: c98be65768f272a89dd24b9454e7837b9dbfe8df584b1ef9cc15ec02af49dd7a
        Code:     PUSH1 0x1
                  PUSH2 0x3e0
                  SHA3
                  PUSH1 0x0
                  SSTORE
        """    
    
        def solve(val):
            results = Z3Solver.instance().get_all_values(constraints, val)
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
        acc_code = unhexlify('60016103e020600055')
            
        acc_balance = constraints.new_bitvec(256, name='balance_0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6')
        constraints.add(acc_balance == 115792089237316195423570985008687907853269984665640564039457584007913129639935)

        acc_nonce = constraints.new_bitvec(256, name='nonce_0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6')
        constraints.add(acc_nonce == 0)

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        caller = 0xcd1722f3947def4cf144679da39c4c32bdc35681
        price = constraints.new_bitvec(256, name='price')
        constraints.add(price == 1)

        value = constraints.new_bitvec(256, name='value')
        constraints.add(value == 115792089237316195423570985008687907853269984665640564039457584007913129639935)

        gas = constraints.new_bitvec(256, name='gas')
        constraints.add(gas == 4294967296)

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
        self.assertEqual(solve(world.block_coinbase()), 0x2adc25665018aa1fe0e6bc666dac8fc2697ff9ba)

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 0)
        self.assertEqual(solve(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 115792089237316195423570985008687907853269984665640564039457584007913129639935)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('60016103e020600055'))
        # check storage
        self.assertEqual(solve(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0xbc36789e7a1e281436464229828f817d6612f7b477d66591ff96a9e064bcc98a)
        # check outs
        self.assertEqual(returndata, unhexlify(''))
        # check logs
        logs = [Log(unhexlify('{:040x}'.format(l.address)), l.topics, solve(l.memlog)) for l in world.logs]
        data = rlp.encode(logs)
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')

        # test used gas
        self.assertEqual(solve(world.current_vm.gas), 4294947153)

    def test_sha3_bigSize(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: sha3_bigSize.json
        sha256sum: 2082e4dc3187961acca04ef10836f496aba47b7f60b28a078da839636be45241
        Code:     PUSH31 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
                  PUSH31 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
                  SHA3
                  PUSH1 0x0
                  SSTORE
        """    
    
        def solve(val):
            results = Z3Solver.instance().get_all_values(constraints, val)
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
        acc_code = unhexlify('7effffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7effffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff20600055')
            
        acc_balance = constraints.new_bitvec(256, name='balance_0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6')
        constraints.add(acc_balance == 115792089237316195423570985008687907853269984665640564039457584007913129639935)

        acc_nonce = constraints.new_bitvec(256, name='nonce_0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6')
        constraints.add(acc_nonce == 0)

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        caller = 0xcd1722f3947def4cf144679da39c4c32bdc35681
        price = constraints.new_bitvec(256, name='price')
        constraints.add(price == 1)

        value = constraints.new_bitvec(256, name='value')
        constraints.add(value == 115792089237316195423570985008687907853269984665640564039457584007913129639935)

        gas = constraints.new_bitvec(256, name='gas')
        constraints.add(gas == 1099511627776)

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
        self.assertEqual(solve(world.block_coinbase()), 0x2adc25665018aa1fe0e6bc666dac8fc2697ff9ba)

        # If test end in exception check it here
        self.assertTrue(result == 'THROW')

    def test_sha3_memSizeQuadraticCost64(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: sha3_memSizeQuadraticCost64.json
        sha256sum: efd3a03ceed3918d998bf6bd6651954eeace410a970db2bad47445b6d8d7e2df
        Code:     PUSH1 0x1
                  PUSH2 0x7e0
                  SHA3
                  PUSH1 0x0
                  SSTORE
        """    
    
        def solve(val):
            results = Z3Solver.instance().get_all_values(constraints, val)
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
        acc_code = unhexlify('60016107e020600055')
            
        acc_balance = constraints.new_bitvec(256, name='balance_0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6')
        constraints.add(acc_balance == 115792089237316195423570985008687907853269984665640564039457584007913129639935)

        acc_nonce = constraints.new_bitvec(256, name='nonce_0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6')
        constraints.add(acc_nonce == 0)

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        caller = 0xcd1722f3947def4cf144679da39c4c32bdc35681
        price = constraints.new_bitvec(256, name='price')
        constraints.add(price == 1)

        value = constraints.new_bitvec(256, name='value')
        constraints.add(value == 115792089237316195423570985008687907853269984665640564039457584007913129639935)

        gas = constraints.new_bitvec(256, name='gas')
        constraints.add(gas == 4294967296)

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
        self.assertEqual(solve(world.block_coinbase()), 0x2adc25665018aa1fe0e6bc666dac8fc2697ff9ba)

        # Add post checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 0)
        self.assertEqual(solve(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 115792089237316195423570985008687907853269984665640564039457584007913129639935)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('60016107e020600055'))
        # check storage
        self.assertEqual(solve(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0xbc36789e7a1e281436464229828f817d6612f7b477d66591ff96a9e064bcc98a)
        # check outs
        self.assertEqual(returndata, unhexlify(''))
        # check logs
        logs = [Log(unhexlify('{:040x}'.format(l.address)), l.topics, solve(l.memlog)) for l in world.logs]
        data = rlp.encode(logs)
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')

        # test used gas
        self.assertEqual(solve(world.current_vm.gas), 4294947051)


if __name__ == '__main__':
    unittest.main()
