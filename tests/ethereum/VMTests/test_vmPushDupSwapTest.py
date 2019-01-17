"""DO NOT MODIFY: Test `/Users/dc/projects/manticore/tests/ethereum/tests/VMTests/vmPushDupSwapTest` generated with make_VMTests.py"""
import unittest
from binascii import unhexlify

import rlp
import sha3
from rlp.sedes import (
    CountableList,
    BigEndianInt,
    Binary,
)

from manticore.core.smtlib import ConstraintSet
from manticore.core.smtlib.visitors import to_constant
from manticore.platforms import evm


class Log(rlp.Serializable):
    fields = [
        ('address', Binary.fixed_length(20, allow_empty=True)),
        ('topics', CountableList(BigEndianInt(32))),
        ('data', Binary())
    ]


class EVMTest_vmPushDupSwapTest(unittest.TestCase):
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

    def test_dup3(self):
        """
        Textcase taken from https://github.com/ethereum/tests
        File: dup3.json
        sha256sum: 6e42a3276a60564e018aaccbbe802d9300a6a730828be4815fd00fbb5c339702
        Code:     PUSH1 0x3
                  PUSH1 0x2
                  PUSH1 0x1
                  DUP3
                  PUSH1 0x3
                  SSTORE
        """    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256,
                             coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('60036002600182600355')
        world.create_account(
            address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
            balance=100000000000000000000000,
            code=bytecode,
            nonce=0
        )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f3947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

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
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        # Add pos checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(world.get_nonce(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), 0)
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 100000000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('60036002600182600355'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x03)), 0x03)
        # check outs
        self.assertEqual(returndata, unhexlify(''))
        # check logs
        logs = [Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs]
        data = rlp.encode(logs)
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test used gas
        self.assertEqual(to_constant(world.current_vm.gas), 79985)

    def test_push13(self):
        """
        Textcase taken from https://github.com/ethereum/tests
        File: push13.json
        sha256sum: 2b83b56b9f62a75aebc6c94f35ab44e64cf1c17583f438722e5aa7ab0036b56d
        Code:     PUSH13 0x33445566778899aabbccddeeff
                  PUSH1 0x3
                  SSTORE
        """    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256,
                             coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('6c33445566778899aabbccddeeff600355')
        world.create_account(
            address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
            balance=100000000000000000000000,
            code=bytecode,
            nonce=0
        )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f3947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

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
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        # Add pos checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(world.get_nonce(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), 0)
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 100000000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('6c33445566778899aabbccddeeff600355'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x03)), 0x33445566778899aabbccddeeff)
        # check outs
        self.assertEqual(returndata, unhexlify(''))
        # check logs
        logs = [Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs]
        data = rlp.encode(logs)
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test used gas
        self.assertEqual(to_constant(world.current_vm.gas), 79994)

    def test_push6(self):
        """
        Textcase taken from https://github.com/ethereum/tests
        File: push6.json
        sha256sum: aab32140caf5d02993fabc2b1c2d5b0a3dc00beb479ad07f44698f76b2204425
        Code:     PUSH6 0xaabbccddeeff
                  PUSH1 0x3
                  SSTORE
        """    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256,
                             coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('65aabbccddeeff600355')
        world.create_account(
            address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
            balance=100000000000000000000000,
            code=bytecode,
            nonce=0
        )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f3947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

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
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        # Add pos checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(world.get_nonce(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), 0)
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 100000000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('65aabbccddeeff600355'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x03)), 0xaabbccddeeff)
        # check outs
        self.assertEqual(returndata, unhexlify(''))
        # check logs
        logs = [Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs]
        data = rlp.encode(logs)
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test used gas
        self.assertEqual(to_constant(world.current_vm.gas), 79994)

    def test_swap4(self):
        """
        Textcase taken from https://github.com/ethereum/tests
        File: swap4.json
        sha256sum: b81d829a7bf564bfc2a4d491c072b9b3e1af5145a8dd7f02c072c9497d3acadc
        Code:     PUSH1 0x4
                  PUSH1 0x3
                  PUSH1 0x2
                  PUSH1 0x1
                  PUSH1 0x3
                  SWAP4
                  SSTORE
        """    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256,
                             coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('600460036002600160039355')
        world.create_account(
            address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
            balance=100000000000000000000000,
            code=bytecode,
            nonce=0
        )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f3947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

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
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        # Add pos checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(world.get_nonce(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), 0)
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 100000000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('600460036002600160039355'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x04)), 0x01)
        # check outs
        self.assertEqual(returndata, unhexlify(''))
        # check logs
        logs = [Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs]
        data = rlp.encode(logs)
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test used gas
        self.assertEqual(to_constant(world.current_vm.gas), 79982)

    def test_dup13(self):
        """
        Textcase taken from https://github.com/ethereum/tests
        File: dup13.json
        sha256sum: c17ffac851203123ccd6a803c979905a0391922a4e128b3e40a6ca44bad3e445
        Code:     PUSH1 0xd
                  PUSH1 0xc
                  PUSH1 0xb
                  PUSH1 0xa
                  PUSH1 0x9
                  PUSH1 0x8
                  PUSH1 0x7
                  PUSH1 0x6
                  PUSH1 0x5
                  PUSH1 0x4
                  PUSH1 0x3
                  PUSH1 0x2
                  PUSH1 0x1
                  DUP13
                  PUSH1 0x3
                  SSTORE
        """    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256,
                             coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('600d600c600b600a6009600860076006600560046003600260018c600355')
        world.create_account(
            address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
            balance=100000000000000000000000,
            code=bytecode,
            nonce=0
        )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f3947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

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
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        # Add pos checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(world.get_nonce(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), 0)
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 100000000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('600d600c600b600a6009600860076006600560046003600260018c600355'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x03)), 0x0d)
        # check outs
        self.assertEqual(returndata, unhexlify(''))
        # check logs
        logs = [Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs]
        data = rlp.encode(logs)
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test used gas
        self.assertEqual(to_constant(world.current_vm.gas), 79955)

    def test_push29(self):
        """
        Textcase taken from https://github.com/ethereum/tests
        File: push29.json
        sha256sum: 132ae21e4a4f8035c435ade1273c6d6318286b6f065cd7be24731941be2051b1
        Code:     PUSH29 0x33445566778899aabbccddeeff00112233445566778899aabbccddeeff
                  PUSH1 0x3
                  SSTORE
        """    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256,
                             coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('7c33445566778899aabbccddeeff00112233445566778899aabbccddeeff600355')
        world.create_account(
            address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
            balance=100000000000000000000000,
            code=bytecode,
            nonce=0
        )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f3947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

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
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        # Add pos checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(world.get_nonce(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), 0)
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 100000000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('7c33445566778899aabbccddeeff00112233445566778899aabbccddeeff600355'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x03)), 0x33445566778899aabbccddeeff00112233445566778899aabbccddeeff)
        # check outs
        self.assertEqual(returndata, unhexlify(''))
        # check logs
        logs = [Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs]
        data = rlp.encode(logs)
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test used gas
        self.assertEqual(to_constant(world.current_vm.gas), 79994)

    def test_swap2error(self):
        """
        Textcase taken from https://github.com/ethereum/tests
        File: swap2error.json
        sha256sum: d35b3a9bb1ee6ea09a066ac6eff54390870d7da23db36ee5ff217320328bd1d4
        Code:     PUSH32 0x10112233445566778899aabbccddeeff00112233445566778899aabbccddeeff
                  PUSH1 0x3
                  SWAP2
                  SSTORE
        """    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256,
                             coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('7f10112233445566778899aabbccddeeff00112233445566778899aabbccddeeff60039155')
        world.create_account(
            address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
            balance=100000000000000000000000,
            code=bytecode,
            nonce=0
        )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f3947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

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
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #If test end in exception check it here
        self.assertTrue(result == 'THROW')

    def test_swap8(self):
        """
        Textcase taken from https://github.com/ethereum/tests
        File: swap8.json
        sha256sum: e1fd8122649ad6ff45e5c57584de60b24c8479ea223135c3de5de94688cf7f01
        Code:     PUSH1 0x8
                  PUSH1 0x7
                  PUSH1 0x6
                  PUSH1 0x5
                  PUSH1 0x4
                  PUSH1 0x3
                  PUSH1 0x2
                  PUSH1 0x1
                  PUSH1 0x3
                  SWAP8
                  SSTORE
        """    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256,
                             coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('6008600760066005600460036002600160039755')
        world.create_account(
            address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
            balance=100000000000000000000000,
            code=bytecode,
            nonce=0
        )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f3947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

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
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        # Add pos checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(world.get_nonce(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), 0)
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 100000000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('6008600760066005600460036002600160039755'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x08)), 0x01)
        # check outs
        self.assertEqual(returndata, unhexlify(''))
        # check logs
        logs = [Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs]
        data = rlp.encode(logs)
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test used gas
        self.assertEqual(to_constant(world.current_vm.gas), 79970)

    def test_push33(self):
        """
        Textcase taken from https://github.com/ethereum/tests
        File: push33.json
        sha256sum: 834c83a78c8a4d81d9c449040c60eebfeb8178eb495cdbfe8a37c7766ad765d2
        Code:     PUSH1 0x65
                  PUSH2 0x7d2
                  PUSH3 0x4a0c7
                  PUSH4 0x26921f4
                  PUSH5 0xbc5588eb1
                  PUSH6 0x372d0f1dca6e
                  PUSH7 0x1ba1d901961c71
                  PUSH8 0xc55f7bc23038e38
                  PUSH9 0x56bc75e2d630fffff
                  PUSH10 0x21e19e0c9bab2400001
                  PUSH11 0x85d1c6e8050f0ea1c71bd
                  PUSH12 0x688be36543f3c36e638e37a
                  PUSH13 0x3d41f73d55d0d482ae5555537
                  PUSH14 0xc76810d0fe03c91964d31c71c6f4
                  PUSH15 0x615dd0360c07d931663b14e38e38b1
                  PUSH16 0x2da3f99955a3adcf27ebb1caaaaaaa6e
                  PUSH17 0x14ccba6a8bb1ed35bd86bf065c71c71c2b
                  PUSH18 0x9491c5d4781b79c9009de6bfb8e38e38de8
                  PUSH19 0x414a0f6fdec81304d4c563e740bffffffffa5
                  PUSH20 0x118427b3b4a05bc8a8a4de845986800000000001
                  PUSH21 0x6eb15e7331e727940d4ac54b7cdca1c71c71c71bd
                  PUSH22 0x567a91c9fefc96ebaa626a22f98c5e638e38e38e37a
                  PUSH23 0x32abd16c5b68006e15d5aa307e383f4e5555555555537
                  PUSH24 0x1a6427bdc4f0d58eab5f48a3ec67f64e21c71c71c71c6f4
                  PUSH25 0x80dd0a0c9b9ff2c2a0c740b06853a0a980ee38e38e38e38b1
                  PUSH26 0x3c679cb5e8f2f9cb3b5d6652b0e7334f746faaaaaaaaaaaaa6e
                  PUSH27 0x1b873815917ebb2bf3b890a1af495d6235bae3c71c71c71c71c2b
                  PUSH28 0x7ae4cca96e1a55dfa49c85ad3c3e60e426b92fb8e38e38e38e38de8
                  PUSH29 0x36018bf074e292bcc7d6c8bea0f9699443046178bffffffffffffffa5
                  PUSH30 0xe7d34c64a9c85d4460dbbca87196b61618a4bd216800000000000000001
                  PUSH31 0x5b901f48a5b994d6572502bc4ea43140486666416aa1c71c71c71c71c71bd
                  PUSH32 0x47889870c178fc477414ea231d70467a388fffe31b4e638e38e38e38e38e37a
        """    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256,
                             coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('60656107d26204a0c763026921f4640bc5588eb165372d0f1dca6e661ba1d901961c71670c55f7bc23038e3868056bc75e2d630fffff69021e19e0c9bab24000016a085d1c6e8050f0ea1c71bd6b0688be36543f3c36e638e37a6c03d41f73d55d0d482ae55555376dc76810d0fe03c91964d31c71c6f46e615dd0360c07d931663b14e38e38b16f2da3f99955a3adcf27ebb1caaaaaaa6e7014ccba6a8bb1ed35bd86bf065c71c71c2b7109491c5d4781b79c9009de6bfb8e38e38de8720414a0f6fdec81304d4c563e740bffffffffa573118427b3b4a05bc8a8a4de8459868000000000017406eb15e7331e727940d4ac54b7cdca1c71c71c71bd750567a91c9fefc96ebaa626a22f98c5e638e38e38e37a76032abd16c5b68006e15d5aa307e383f4e55555555555377701a6427bdc4f0d58eab5f48a3ec67f64e21c71c71c71c6f478080dd0a0c9b9ff2c2a0c740b06853a0a980ee38e38e38e38b17903c679cb5e8f2f9cb3b5d6652b0e7334f746faaaaaaaaaaaaa6e7a01b873815917ebb2bf3b890a1af495d6235bae3c71c71c71c71c2b7b07ae4cca96e1a55dfa49c85ad3c3e60e426b92fb8e38e38e38e38de87c036018bf074e292bcc7d6c8bea0f9699443046178bffffffffffffffa57d0e7d34c64a9c85d4460dbbca87196b61618a4bd2168000000000000000017e05b901f48a5b994d6572502bc4ea43140486666416aa1c71c71c71c71c71bd7f047889870c178fc477414ea231d70467a388fffe31b4e638e38e38e38e38e37a')
        world.create_account(
            address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
            balance=100000000000000000000000,
            code=bytecode,
            nonce=0
        )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f3947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 32

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
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #If test end in exception check it here
        self.assertTrue(result == 'THROW')

    def test_push25(self):
        """
        Textcase taken from https://github.com/ethereum/tests
        File: push25.json
        sha256sum: afef30db893e37e4edb2a0a011242c23fa903d740ac8240845693a66cb8de625
        Code:     PUSH25 0x778899aabbccddeeff00112233445566778899aabbccddeeff
                  PUSH1 0x3
                  SSTORE
        """    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256,
                             coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('78778899aabbccddeeff00112233445566778899aabbccddeeff600355')
        world.create_account(
            address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
            balance=100000000000000000000000,
            code=bytecode,
            nonce=0
        )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f3947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

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
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        # Add pos checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(world.get_nonce(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), 0)
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 100000000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('78778899aabbccddeeff00112233445566778899aabbccddeeff600355'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x03)), 0x778899aabbccddeeff00112233445566778899aabbccddeeff)
        # check outs
        self.assertEqual(returndata, unhexlify(''))
        # check logs
        logs = [Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs]
        data = rlp.encode(logs)
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test used gas
        self.assertEqual(to_constant(world.current_vm.gas), 79994)

    def test_swap10(self):
        """
        Textcase taken from https://github.com/ethereum/tests
        File: swap10.json
        sha256sum: 1e176ce876a6f9094f4b2ec17c2d6f62fa018bd1253bf4161512018b36aaa10f
        Code:     PUSH1 0xa
                  PUSH1 0x9
                  PUSH1 0x8
                  PUSH1 0x7
                  PUSH1 0x6
                  PUSH1 0x5
                  PUSH1 0x4
                  PUSH1 0x3
                  PUSH1 0x2
                  PUSH1 0x1
                  PUSH1 0x3
                  SWAP10
                  SSTORE
        """    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256,
                             coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('600a60096008600760066005600460036002600160039955')
        world.create_account(
            address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
            balance=100000000000000000000000,
            code=bytecode,
            nonce=0
        )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f3947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

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
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        # Add pos checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(world.get_nonce(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), 0)
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 100000000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('600a60096008600760066005600460036002600160039955'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x0a)), 0x01)
        # check outs
        self.assertEqual(returndata, unhexlify(''))
        # check logs
        logs = [Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs]
        data = rlp.encode(logs)
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test used gas
        self.assertEqual(to_constant(world.current_vm.gas), 79964)

    def test_swap11(self):
        """
        Textcase taken from https://github.com/ethereum/tests
        File: swap11.json
        sha256sum: a84d7b8088c736e55b63e16ecf997859bb82115ef75a3b71d113c9caa4c7ac1a
        Code:     PUSH1 0xb
                  PUSH1 0xa
                  PUSH1 0x9
                  PUSH1 0x8
                  PUSH1 0x7
                  PUSH1 0x6
                  PUSH1 0x5
                  PUSH1 0x4
                  PUSH1 0x3
                  PUSH1 0x2
                  PUSH1 0x1
                  PUSH1 0x3
                  SWAP11
                  SSTORE
        """    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256,
                             coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('600b600a60096008600760066005600460036002600160039a55')
        world.create_account(
            address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
            balance=100000000000000000000000,
            code=bytecode,
            nonce=0
        )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f3947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

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
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        # Add pos checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(world.get_nonce(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), 0)
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 100000000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('600b600a60096008600760066005600460036002600160039a55'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x0b)), 0x01)
        # check outs
        self.assertEqual(returndata, unhexlify(''))
        # check logs
        logs = [Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs]
        data = rlp.encode(logs)
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test used gas
        self.assertEqual(to_constant(world.current_vm.gas), 79961)

    def test_push24(self):
        """
        Textcase taken from https://github.com/ethereum/tests
        File: push24.json
        sha256sum: 32dab868d9ff16ad9f3e0ea1a7bc52b3563922104195804409a1372a790b979b
        Code:     PUSH24 0x8899aabbccddeeff00112233445566778899aabbccddeeff
                  PUSH1 0x3
                  SSTORE
        """    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256,
                             coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('778899aabbccddeeff00112233445566778899aabbccddeeff600355')
        world.create_account(
            address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
            balance=100000000000000000000000,
            code=bytecode,
            nonce=0
        )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f3947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

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
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        # Add pos checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(world.get_nonce(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), 0)
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 100000000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('778899aabbccddeeff00112233445566778899aabbccddeeff600355'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x03)), 0x8899aabbccddeeff00112233445566778899aabbccddeeff)
        # check outs
        self.assertEqual(returndata, unhexlify(''))
        # check logs
        logs = [Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs]
        data = rlp.encode(logs)
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test used gas
        self.assertEqual(to_constant(world.current_vm.gas), 79994)

    def test_push32(self):
        """
        Textcase taken from https://github.com/ethereum/tests
        File: push32.json
        sha256sum: 10bf6eec99511da1bad139928ac01848618a60d009e9105812bc46dc2f963dae
        Code:     PUSH32 0x10112233445566778899aabbccddeeff00112233445566778899aabbccddeeff
                  PUSH1 0x3
                  SSTORE
        """    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256,
                             coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('7f10112233445566778899aabbccddeeff00112233445566778899aabbccddeeff600355')
        world.create_account(
            address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
            balance=100000000000000000000000,
            code=bytecode,
            nonce=0
        )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f3947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

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
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        # Add pos checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(world.get_nonce(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), 0)
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 100000000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('7f10112233445566778899aabbccddeeff00112233445566778899aabbccddeeff600355'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x03)), 0x10112233445566778899aabbccddeeff00112233445566778899aabbccddeeff)
        # check outs
        self.assertEqual(returndata, unhexlify(''))
        # check logs
        logs = [Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs]
        data = rlp.encode(logs)
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test used gas
        self.assertEqual(to_constant(world.current_vm.gas), 79994)

    def test_swap9(self):
        """
        Textcase taken from https://github.com/ethereum/tests
        File: swap9.json
        sha256sum: 1a5190f0995e162b9cd993290467561b263cf043c114303ea72495604f55f481
        Code:     PUSH1 0x9
                  PUSH1 0x8
                  PUSH1 0x7
                  PUSH1 0x6
                  PUSH1 0x5
                  PUSH1 0x4
                  PUSH1 0x3
                  PUSH1 0x2
                  PUSH1 0x1
                  PUSH1 0x3
                  SWAP9
                  SSTORE
        """    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256,
                             coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('60096008600760066005600460036002600160039855')
        world.create_account(
            address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
            balance=100000000000000000000000,
            code=bytecode,
            nonce=0
        )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f3947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

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
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        # Add pos checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(world.get_nonce(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), 0)
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 100000000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('60096008600760066005600460036002600160039855'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x09)), 0x01)
        # check outs
        self.assertEqual(returndata, unhexlify(''))
        # check logs
        logs = [Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs]
        data = rlp.encode(logs)
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test used gas
        self.assertEqual(to_constant(world.current_vm.gas), 79967)

    def test_push28(self):
        """
        Textcase taken from https://github.com/ethereum/tests
        File: push28.json
        sha256sum: 2a6daa645780c08f9db84a439752eef9b92dd6842df3ba309afe344ee4417bfe
        Code:     PUSH28 0x445566778899aabbccddeeff00112233445566778899aabbccddeeff
                  PUSH1 0x3
                  SSTORE
        """    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256,
                             coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('7b445566778899aabbccddeeff00112233445566778899aabbccddeeff600355')
        world.create_account(
            address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
            balance=100000000000000000000000,
            code=bytecode,
            nonce=0
        )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f3947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

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
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        # Add pos checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(world.get_nonce(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), 0)
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 100000000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('7b445566778899aabbccddeeff00112233445566778899aabbccddeeff600355'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x03)), 0x445566778899aabbccddeeff00112233445566778899aabbccddeeff)
        # check outs
        self.assertEqual(returndata, unhexlify(''))
        # check logs
        logs = [Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs]
        data = rlp.encode(logs)
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test used gas
        self.assertEqual(to_constant(world.current_vm.gas), 79994)

    def test_swap5(self):
        """
        Textcase taken from https://github.com/ethereum/tests
        File: swap5.json
        sha256sum: e7fc1b3e6d228d74e95ae3496ec1a83c68441007fb5e883fd66c9ba91bde9bb6
        Code:     PUSH1 0x5
                  PUSH1 0x4
                  PUSH1 0x3
                  PUSH1 0x2
                  PUSH1 0x1
                  PUSH1 0x3
                  SWAP5
                  SSTORE
        """    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256,
                             coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('6005600460036002600160039455')
        world.create_account(
            address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
            balance=100000000000000000000000,
            code=bytecode,
            nonce=0
        )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f3947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

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
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        # Add pos checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(world.get_nonce(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), 0)
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 100000000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('6005600460036002600160039455'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x05)), 0x01)
        # check outs
        self.assertEqual(returndata, unhexlify(''))
        # check logs
        logs = [Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs]
        data = rlp.encode(logs)
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test used gas
        self.assertEqual(to_constant(world.current_vm.gas), 79979)

    def test_dup12(self):
        """
        Textcase taken from https://github.com/ethereum/tests
        File: dup12.json
        sha256sum: d1245f700ff5fba2563633b3a60277d8002f58af43f6c5d445ad8d5f57dde1e1
        Code:     PUSH1 0xc
                  PUSH1 0xb
                  PUSH1 0xa
                  PUSH1 0x9
                  PUSH1 0x8
                  PUSH1 0x7
                  PUSH1 0x6
                  PUSH1 0x5
                  PUSH1 0x4
                  PUSH1 0x3
                  PUSH1 0x2
                  PUSH1 0x1
                  DUP12
                  PUSH1 0x3
                  SSTORE
        """    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256,
                             coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('600c600b600a6009600860076006600560046003600260018b600355')
        world.create_account(
            address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
            balance=100000000000000000000000,
            code=bytecode,
            nonce=0
        )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f3947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

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
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        # Add pos checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(world.get_nonce(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), 0)
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 100000000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('600c600b600a6009600860076006600560046003600260018b600355'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x03)), 0x0c)
        # check outs
        self.assertEqual(returndata, unhexlify(''))
        # check logs
        logs = [Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs]
        data = rlp.encode(logs)
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test used gas
        self.assertEqual(to_constant(world.current_vm.gas), 79958)

    def test_push7(self):
        """
        Textcase taken from https://github.com/ethereum/tests
        File: push7.json
        sha256sum: efb306cab0ce72764dd4b0f955c354a6dc4f6a35c54d8d4a3fc63fd723e84a91
        Code:     PUSH7 0x99aabbccddeeff
                  PUSH1 0x3
                  SSTORE
        """    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256,
                             coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('6699aabbccddeeff600355')
        world.create_account(
            address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
            balance=100000000000000000000000,
            code=bytecode,
            nonce=0
        )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f3947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

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
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        # Add pos checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(world.get_nonce(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), 0)
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 100000000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('6699aabbccddeeff600355'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x03)), 0x99aabbccddeeff)
        # check outs
        self.assertEqual(returndata, unhexlify(''))
        # check logs
        logs = [Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs]
        data = rlp.encode(logs)
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test used gas
        self.assertEqual(to_constant(world.current_vm.gas), 79994)

    def test_push12(self):
        """
        Textcase taken from https://github.com/ethereum/tests
        File: push12.json
        sha256sum: f3b084c991134bff01965593220b3296adc0f3a4d1cb8d0ff273259f5014676b
        Code:     PUSH12 0x445566778899aabbccddeeff
                  PUSH1 0x3
                  SSTORE
        """    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256,
                             coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('6b445566778899aabbccddeeff600355')
        world.create_account(
            address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
            balance=100000000000000000000000,
            code=bytecode,
            nonce=0
        )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f3947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

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
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        # Add pos checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(world.get_nonce(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), 0)
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 100000000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('6b445566778899aabbccddeeff600355'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x03)), 0x445566778899aabbccddeeff)
        # check outs
        self.assertEqual(returndata, unhexlify(''))
        # check logs
        logs = [Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs]
        data = rlp.encode(logs)
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test used gas
        self.assertEqual(to_constant(world.current_vm.gas), 79994)

    def test_dup2(self):
        """
        Textcase taken from https://github.com/ethereum/tests
        File: dup2.json
        sha256sum: a10d6a4e70421383833d99f8d6dd6f8788f7a3f850594fa0eda8048991a4c741
        Code:     PUSH1 0x2
                  PUSH1 0x1
                  DUP2
                  PUSH1 0x3
                  SSTORE
        """    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256,
                             coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('6002600181600355')
        world.create_account(
            address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
            balance=100000000000000000000000,
            code=bytecode,
            nonce=0
        )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f3947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

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
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        # Add pos checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(world.get_nonce(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), 0)
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 100000000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('6002600181600355'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x03)), 0x02)
        # check outs
        self.assertEqual(returndata, unhexlify(''))
        # check logs
        logs = [Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs]
        data = rlp.encode(logs)
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test used gas
        self.assertEqual(to_constant(world.current_vm.gas), 79988)

    def test_dup9(self):
        """
        Textcase taken from https://github.com/ethereum/tests
        File: dup9.json
        sha256sum: 251eae71e8409104471b500149f4fedc2b29f95a8afa1e507f842948c960b865
        Code:     PUSH1 0x9
                  PUSH1 0x8
                  PUSH1 0x7
                  PUSH1 0x6
                  PUSH1 0x5
                  PUSH1 0x4
                  PUSH1 0x3
                  PUSH1 0x2
                  PUSH1 0x1
                  DUP9
                  PUSH1 0x3
                  SSTORE
        """    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256,
                             coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('60096008600760066005600460036002600188600355')
        world.create_account(
            address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
            balance=100000000000000000000000,
            code=bytecode,
            nonce=0
        )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f3947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

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
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        # Add pos checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(world.get_nonce(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), 0)
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 100000000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('60096008600760066005600460036002600188600355'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x03)), 0x09)
        # check outs
        self.assertEqual(returndata, unhexlify(''))
        # check logs
        logs = [Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs]
        data = rlp.encode(logs)
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test used gas
        self.assertEqual(to_constant(world.current_vm.gas), 79967)

    def test_push19(self):
        """
        Textcase taken from https://github.com/ethereum/tests
        File: push19.json
        sha256sum: d7ab5742487922199b403b47127f5badc1a3deced2ef57655a264369a1263269
        Code:     PUSH19 0xddeeff00112233445566778899aabbccddeeff
                  PUSH1 0x3
                  SSTORE
        """    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256,
                             coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('72ddeeff00112233445566778899aabbccddeeff600355')
        world.create_account(
            address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
            balance=100000000000000000000000,
            code=bytecode,
            nonce=0
        )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f3947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

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
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        # Add pos checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(world.get_nonce(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), 0)
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 100000000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('72ddeeff00112233445566778899aabbccddeeff600355'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x03)), 0xddeeff00112233445566778899aabbccddeeff)
        # check outs
        self.assertEqual(returndata, unhexlify(''))
        # check logs
        logs = [Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs]
        data = rlp.encode(logs)
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test used gas
        self.assertEqual(to_constant(world.current_vm.gas), 79994)

    def test_push23(self):
        """
        Textcase taken from https://github.com/ethereum/tests
        File: push23.json
        sha256sum: 37cd035463d208af275bc935e0b0545e81dc7c0e69c78e066ab7d8b187dc3a47
        Code:     PUSH23 0x99aabbccddeeff00112233445566778899aabbccddeeff
                  PUSH1 0x3
                  SSTORE
        """    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256,
                             coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('7699aabbccddeeff00112233445566778899aabbccddeeff600355')
        world.create_account(
            address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
            balance=100000000000000000000000,
            code=bytecode,
            nonce=0
        )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f3947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

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
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        # Add pos checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(world.get_nonce(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), 0)
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 100000000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('7699aabbccddeeff00112233445566778899aabbccddeeff600355'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x03)), 0x99aabbccddeeff00112233445566778899aabbccddeeff)
        # check outs
        self.assertEqual(returndata, unhexlify(''))
        # check logs
        logs = [Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs]
        data = rlp.encode(logs)
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test used gas
        self.assertEqual(to_constant(world.current_vm.gas), 79994)

    def test_swap16(self):
        """
        Textcase taken from https://github.com/ethereum/tests
        File: swap16.json
        sha256sum: bf70a7e7db62a8c9d236c455888f30516c351442e5e6e3b7b93d2ed4ad6b18fe
        Code:     PUSH1 0x10
                  PUSH1 0xf
                  PUSH1 0xe
                  PUSH1 0xd
                  PUSH1 0xc
                  PUSH1 0xb
                  PUSH1 0xa
                  PUSH1 0x9
                  PUSH1 0x8
                  PUSH1 0x7
                  PUSH1 0x6
                  PUSH1 0x5
                  PUSH1 0x4
                  PUSH1 0x3
                  PUSH1 0x2
                  PUSH1 0x1
                  PUSH1 0x3
                  SWAP16
                  SSTORE
        """    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256,
                             coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('6010600f600e600d600c600b600a60096008600760066005600460036002600160039f55')
        world.create_account(
            address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
            balance=100000000000000000000000,
            code=bytecode,
            nonce=0
        )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f3947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

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
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        # Add pos checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(world.get_nonce(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), 0)
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 100000000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('6010600f600e600d600c600b600a60096008600760066005600460036002600160039f55'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x10)), 0x01)
        # check outs
        self.assertEqual(returndata, unhexlify(''))
        # check logs
        logs = [Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs]
        data = rlp.encode(logs)
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test used gas
        self.assertEqual(to_constant(world.current_vm.gas), 79946)

    def test_dup5(self):
        """
        Textcase taken from https://github.com/ethereum/tests
        File: dup5.json
        sha256sum: 602513c6572e4a6d9e02ae0f22576b379d5b239af261cfe1f8d416623c2623a7
        Code:     PUSH1 0x5
                  PUSH1 0x4
                  PUSH1 0x3
                  PUSH1 0x2
                  PUSH1 0x1
                  DUP5
                  PUSH1 0x3
                  SSTORE
        """    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256,
                             coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('6005600460036002600184600355')
        world.create_account(
            address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
            balance=100000000000000000000000,
            code=bytecode,
            nonce=0
        )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f3947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

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
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        # Add pos checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(world.get_nonce(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), 0)
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 100000000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('6005600460036002600184600355'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x03)), 0x05)
        # check outs
        self.assertEqual(returndata, unhexlify(''))
        # check logs
        logs = [Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs]
        data = rlp.encode(logs)
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test used gas
        self.assertEqual(to_constant(world.current_vm.gas), 79979)

    def test_push32AndSuicide(self):
        """
        Textcase taken from https://github.com/ethereum/tests
        File: push32AndSuicide.json
        sha256sum: 3abbcdea7d3a9679bc0468b0c925a7e18a31dc7dbbf7ce3efee30956af345b20
        Code:     PUSH32 0xff10112233445566778899aabbccddeeff00112233445566778899aabbccddee
                  SELFDESTRUCT
                  PUSH1 0x3
                  SSTORE
        """    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256,
                             coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('7fff10112233445566778899aabbccddeeff00112233445566778899aabbccddeeff600355')
        world.create_account(
            address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
            balance=100000000000000000000000,
            code=bytecode,
            nonce=0
        )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f3947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

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
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        # Add pos checks for account 0xbbccddeeff00112233445566778899aabbccddee
        # check nonce, balance, code
        self.assertEqual(world.get_nonce(0xbbccddeeff00112233445566778899aabbccddee), 0)
        self.assertEqual(to_constant(world.get_balance(0xbbccddeeff00112233445566778899aabbccddee)), 100000000000000000000000)
        self.assertEqual(world.get_code(0xbbccddeeff00112233445566778899aabbccddee), unhexlify(''))
        # check outs
        self.assertEqual(returndata, unhexlify(''))
        # check logs
        logs = [Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs]
        data = rlp.encode(logs)
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test used gas
        self.assertEqual(to_constant(world.current_vm.gas), 99997)

    def test_push15(self):
        """
        Textcase taken from https://github.com/ethereum/tests
        File: push15.json
        sha256sum: 6c6fb91cc5429627652b0d19a77c276f92b644d41d5f737ffc57ff3997748583
        Code:     PUSH15 0x112233445566778899aabbccddeeff
                  PUSH1 0x3
                  SSTORE
        """    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256,
                             coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('6e112233445566778899aabbccddeeff600355')
        world.create_account(
            address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
            balance=100000000000000000000000,
            code=bytecode,
            nonce=0
        )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f3947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

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
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        # Add pos checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(world.get_nonce(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), 0)
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 100000000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('6e112233445566778899aabbccddeeff600355'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x03)), 0x112233445566778899aabbccddeeff)
        # check outs
        self.assertEqual(returndata, unhexlify(''))
        # check logs
        logs = [Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs]
        data = rlp.encode(logs)
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test used gas
        self.assertEqual(to_constant(world.current_vm.gas), 79994)

    def test_push32Undefined3(self):
        """
        Textcase taken from https://github.com/ethereum/tests
        File: push32Undefined3.json
        sha256sum: f02902689097ff0d3abaa241f98172a7affe62aefed41dcb6269ee5239799e2e
        Code:     
        """    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256,
                             coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('7f')
        world.create_account(
            address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
            balance=100000000000000000000000,
            code=bytecode,
            nonce=0
        )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f3947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

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
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        # Add pos checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(world.get_nonce(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), 0)
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 100000000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('7f'))
        # check outs
        self.assertEqual(returndata, unhexlify(''))
        # check logs
        logs = [Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs]
        data = rlp.encode(logs)
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test used gas
        self.assertEqual(to_constant(world.current_vm.gas), 99997)

    def test_dup15(self):
        """
        Textcase taken from https://github.com/ethereum/tests
        File: dup15.json
        sha256sum: c611b8a5adc27e1738eb20d31b0ecbcaa342be7bd9b68a74da7470fb9aa5a133
        Code:     PUSH1 0xf
                  PUSH1 0xe
                  PUSH1 0xd
                  PUSH1 0xc
                  PUSH1 0xb
                  PUSH1 0xa
                  PUSH1 0x9
                  PUSH1 0x8
                  PUSH1 0x7
                  PUSH1 0x6
                  PUSH1 0x5
                  PUSH1 0x4
                  PUSH1 0x3
                  PUSH1 0x2
                  PUSH1 0x1
                  DUP15
                  PUSH1 0x3
                  SSTORE
        """    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256,
                             coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('600f600e600d600c600b600a6009600860076006600560046003600260018e600355')
        world.create_account(
            address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
            balance=100000000000000000000000,
            code=bytecode,
            nonce=0
        )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f3947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

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
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        # Add pos checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(world.get_nonce(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), 0)
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 100000000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('600f600e600d600c600b600a6009600860076006600560046003600260018e600355'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x03)), 0x0f)
        # check outs
        self.assertEqual(returndata, unhexlify(''))
        # check logs
        logs = [Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs]
        data = rlp.encode(logs)
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test used gas
        self.assertEqual(to_constant(world.current_vm.gas), 79949)

    def test_swap2(self):
        """
        Textcase taken from https://github.com/ethereum/tests
        File: swap2.json
        sha256sum: 0db5c674237609f6d0352f138351cc76fb7813162125152f59f51818b9a79baf
        Code:     PUSH1 0x2
                  PUSH1 0x1
                  PUSH1 0x3
                  SWAP2
                  SSTORE
        """    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256,
                             coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('6002600160039155')
        world.create_account(
            address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
            balance=100000000000000000000000,
            code=bytecode,
            nonce=0
        )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f3947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

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
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        # Add pos checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(world.get_nonce(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), 0)
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 100000000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('6002600160039155'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x02)), 0x01)
        # check outs
        self.assertEqual(returndata, unhexlify(''))
        # check logs
        logs = [Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs]
        data = rlp.encode(logs)
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test used gas
        self.assertEqual(to_constant(world.current_vm.gas), 79988)

    def test_push32Undefined2(self):
        """
        Textcase taken from https://github.com/ethereum/tests
        File: push32Undefined2.json
        sha256sum: 56eeb29d8e53557533409647e7385183baf01550292e86699647b8789de1bc21
        Code:     PUSH32 0x102030000000000000000000000000000000000000000000000000000000000
                  PUSH1 0x0
                  SSTORE
        """    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256,
                             coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('7f0102030000000000000000000000000000000000000000000000000000000000600055')
        world.create_account(
            address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
            balance=100000000000000000000000,
            code=bytecode,
            nonce=0
        )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f3947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

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
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        # Add pos checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(world.get_nonce(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), 0)
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 100000000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('7f0102030000000000000000000000000000000000000000000000000000000000600055'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0x0102030000000000000000000000000000000000000000000000000000000000)
        # check outs
        self.assertEqual(returndata, unhexlify(''))
        # check logs
        logs = [Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs]
        data = rlp.encode(logs)
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test used gas
        self.assertEqual(to_constant(world.current_vm.gas), 79994)

    def test_dup14(self):
        """
        Textcase taken from https://github.com/ethereum/tests
        File: dup14.json
        sha256sum: 42cf53e96cb91798c563da1142837676ade198d03255b8033712b234f6fcb766
        Code:     PUSH1 0xe
                  PUSH1 0xd
                  PUSH1 0xc
                  PUSH1 0xb
                  PUSH1 0xa
                  PUSH1 0x9
                  PUSH1 0x8
                  PUSH1 0x7
                  PUSH1 0x6
                  PUSH1 0x5
                  PUSH1 0x4
                  PUSH1 0x3
                  PUSH1 0x2
                  PUSH1 0x1
                  DUP14
                  PUSH1 0x3
                  SSTORE
        """    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256,
                             coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('600e600d600c600b600a6009600860076006600560046003600260018d600355')
        world.create_account(
            address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
            balance=100000000000000000000000,
            code=bytecode,
            nonce=0
        )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f3947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

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
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        # Add pos checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(world.get_nonce(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), 0)
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 100000000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('600e600d600c600b600a6009600860076006600560046003600260018d600355'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x03)), 0x0e)
        # check outs
        self.assertEqual(returndata, unhexlify(''))
        # check logs
        logs = [Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs]
        data = rlp.encode(logs)
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test used gas
        self.assertEqual(to_constant(world.current_vm.gas), 79952)

    def test_swap3(self):
        """
        Textcase taken from https://github.com/ethereum/tests
        File: swap3.json
        sha256sum: f447f0c75fef2ef72db556ef06af489e7715779a44d3423a016463c986b3ec50
        Code:     PUSH1 0x3
                  PUSH1 0x2
                  PUSH1 0x1
                  PUSH1 0x3
                  SWAP3
                  SSTORE
        """    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256,
                             coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('60036002600160039255')
        world.create_account(
            address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
            balance=100000000000000000000000,
            code=bytecode,
            nonce=0
        )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f3947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

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
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        # Add pos checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(world.get_nonce(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), 0)
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 100000000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('60036002600160039255'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x03)), 0x01)
        # check outs
        self.assertEqual(returndata, unhexlify(''))
        # check logs
        logs = [Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs]
        data = rlp.encode(logs)
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test used gas
        self.assertEqual(to_constant(world.current_vm.gas), 79985)

    def test_swapjump1(self):
        """
        Textcase taken from https://github.com/ethereum/tests
        File: swapjump1.json
        sha256sum: 5ba15c94dfcc88f212aaff0f5bd9c267f55bfa477336fa372d810417f856985a
        Code:     PUSH1 0x5
                  PUSH1 0x2
                  PUSH1 0x1
                  PUSH1 0xc
                  JUMPI
                  POP
                  POP
                  STOP
                  JUMPDEST
                  SWAP1
                  PUSH1 0x1
                  PUSH2 0x1657
                  POP
                  POP
                  STOP
                  JUMPDEST
                  SUB
                  JUMPDEST
                  SUB
                  PUSH1 0x0
                  MSTORE
                  PUSH1 0x1
                  PUSH1 0x3
                  PUSH2 0x1ff3
        """    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256,
                             coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('600560026001600c575050005b9060016116575050005b035b0360005260016003611ff3')
        world.create_account(
            address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
            balance=100000000000000000000000,
            code=bytecode,
            nonce=0
        )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f3947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

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
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        # Add pos checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(world.get_nonce(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), 0)
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 100000000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('600560026001600c575050005b9060016116575050005b035b0360005260016003611ff3'))
        # check outs
        self.assertEqual(returndata, unhexlify(''))
        # check logs
        logs = [Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs]
        data = rlp.encode(logs)
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test used gas
        self.assertEqual(to_constant(world.current_vm.gas), 99964)

    def test_push1(self):
        """
        Textcase taken from https://github.com/ethereum/tests
        File: push1.json
        sha256sum: cb47fb054f4a67c763d0876f4838c2a0f42c4f35fc042be86e8d7af067d3329b
        Code:     PUSH1 0xff
                  PUSH1 0x3
                  SSTORE
        """    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256,
                             coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('60ff600355')
        world.create_account(
            address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
            balance=100000000000000000000000,
            code=bytecode,
            nonce=0
        )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f3947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

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
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        # Add pos checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(world.get_nonce(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), 0)
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 100000000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('60ff600355'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x03)), 0xff)
        # check outs
        self.assertEqual(returndata, unhexlify(''))
        # check logs
        logs = [Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs]
        data = rlp.encode(logs)
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test used gas
        self.assertEqual(to_constant(world.current_vm.gas), 79994)

    def test_push14(self):
        """
        Textcase taken from https://github.com/ethereum/tests
        File: push14.json
        sha256sum: 3adaab5256baba44e9a1775aa40501ca4b9c8191f5db0447a89c166146632b48
        Code:     PUSH14 0x2233445566778899aabbccddeeff
                  PUSH1 0x3
                  SSTORE
        """    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256,
                             coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('6d2233445566778899aabbccddeeff600355')
        world.create_account(
            address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
            balance=100000000000000000000000,
            code=bytecode,
            nonce=0
        )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f3947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

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
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        # Add pos checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(world.get_nonce(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), 0)
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 100000000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('6d2233445566778899aabbccddeeff600355'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x03)), 0x2233445566778899aabbccddeeff)
        # check outs
        self.assertEqual(returndata, unhexlify(''))
        # check logs
        logs = [Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs]
        data = rlp.encode(logs)
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test used gas
        self.assertEqual(to_constant(world.current_vm.gas), 79994)

    def test_dup4(self):
        """
        Textcase taken from https://github.com/ethereum/tests
        File: dup4.json
        sha256sum: b6e118fc01e20bf050982fad4df1003b9220050071b53011763891db90af1a9c
        Code:     PUSH1 0x4
                  PUSH1 0x3
                  PUSH1 0x2
                  PUSH1 0x1
                  DUP4
                  PUSH1 0x3
                  SSTORE
        """    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256,
                             coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('600460036002600183600355')
        world.create_account(
            address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
            balance=100000000000000000000000,
            code=bytecode,
            nonce=0
        )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f3947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

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
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        # Add pos checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(world.get_nonce(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), 0)
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 100000000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('600460036002600183600355'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x03)), 0x04)
        # check outs
        self.assertEqual(returndata, unhexlify(''))
        # check logs
        logs = [Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs]
        data = rlp.encode(logs)
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test used gas
        self.assertEqual(to_constant(world.current_vm.gas), 79982)

    def test_push22(self):
        """
        Textcase taken from https://github.com/ethereum/tests
        File: push22.json
        sha256sum: 6b8ecab8300c80694ab8cc8ebc1f7440d6060b7634fdecc6107287abc376a374
        Code:     PUSH22 0xaabbccddeeff00112233445566778899aabbccddeeff
                  PUSH1 0x3
                  SSTORE
        """    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256,
                             coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('75aabbccddeeff00112233445566778899aabbccddeeff600355')
        world.create_account(
            address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
            balance=100000000000000000000000,
            code=bytecode,
            nonce=0
        )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f3947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

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
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        # Add pos checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(world.get_nonce(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), 0)
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 100000000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('75aabbccddeeff00112233445566778899aabbccddeeff600355'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x03)), 0xaabbccddeeff00112233445566778899aabbccddeeff)
        # check outs
        self.assertEqual(returndata, unhexlify(''))
        # check logs
        logs = [Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs]
        data = rlp.encode(logs)
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test used gas
        self.assertEqual(to_constant(world.current_vm.gas), 79994)

    def test_push18(self):
        """
        Textcase taken from https://github.com/ethereum/tests
        File: push18.json
        sha256sum: 4d49fce4eecfd8306e27e40747858a66695a8687c841a26ff1f831293668cca9
        Code:     PUSH18 0xeeff00112233445566778899aabbccddeeff
                  PUSH1 0x3
                  SSTORE
        """    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256,
                             coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('71eeff00112233445566778899aabbccddeeff600355')
        world.create_account(
            address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
            balance=100000000000000000000000,
            code=bytecode,
            nonce=0
        )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f3947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

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
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        # Add pos checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(world.get_nonce(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), 0)
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 100000000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('71eeff00112233445566778899aabbccddeeff600355'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x03)), 0xeeff00112233445566778899aabbccddeeff)
        # check outs
        self.assertEqual(returndata, unhexlify(''))
        # check logs
        logs = [Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs]
        data = rlp.encode(logs)
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test used gas
        self.assertEqual(to_constant(world.current_vm.gas), 79994)

    def test_dup8(self):
        """
        Textcase taken from https://github.com/ethereum/tests
        File: dup8.json
        sha256sum: 2fc9c945615bbc602de27a4cae8a15b19211cae8ab00f22080680bf0c0794d5d
        Code:     PUSH1 0x8
                  PUSH1 0x7
                  PUSH1 0x6
                  PUSH1 0x5
                  PUSH1 0x4
                  PUSH1 0x3
                  PUSH1 0x2
                  PUSH1 0x1
                  DUP8
                  PUSH1 0x3
                  SSTORE
        """    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256,
                             coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('6008600760066005600460036002600187600355')
        world.create_account(
            address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
            balance=100000000000000000000000,
            code=bytecode,
            nonce=0
        )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f3947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

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
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        # Add pos checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(world.get_nonce(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), 0)
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 100000000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('6008600760066005600460036002600187600355'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x03)), 0x08)
        # check outs
        self.assertEqual(returndata, unhexlify(''))
        # check logs
        logs = [Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs]
        data = rlp.encode(logs)
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test used gas
        self.assertEqual(to_constant(world.current_vm.gas), 79970)

    def test_swap14(self):
        """
        Textcase taken from https://github.com/ethereum/tests
        File: swap14.json
        sha256sum: accff146855dc097cc5c5f21bb8685f3f40fd3be335ca1c6dcafc5cd8789e9bb
        Code:     PUSH1 0xe
                  PUSH1 0xd
                  PUSH1 0xc
                  PUSH1 0xb
                  PUSH1 0xa
                  PUSH1 0x9
                  PUSH1 0x8
                  PUSH1 0x7
                  PUSH1 0x6
                  PUSH1 0x5
                  PUSH1 0x4
                  PUSH1 0x3
                  PUSH1 0x2
                  PUSH1 0x1
                  PUSH1 0x3
                  SWAP14
                  SSTORE
        """    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256,
                             coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('600e600d600c600b600a60096008600760066005600460036002600160039d55')
        world.create_account(
            address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
            balance=100000000000000000000000,
            code=bytecode,
            nonce=0
        )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f3947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

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
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        # Add pos checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(world.get_nonce(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), 0)
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 100000000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('600e600d600c600b600a60096008600760066005600460036002600160039d55'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x0e)), 0x01)
        # check outs
        self.assertEqual(returndata, unhexlify(''))
        # check logs
        logs = [Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs]
        data = rlp.encode(logs)
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test used gas
        self.assertEqual(to_constant(world.current_vm.gas), 79952)

    def test_push21(self):
        """
        Textcase taken from https://github.com/ethereum/tests
        File: push21.json
        sha256sum: 2d6516046733e55d635aeabebcd74472e2674c28d73ebc4b632e5a27b170d1e2
        Code:     PUSH21 0xbbccddeeff00112233445566778899aabbccddeeff
                  PUSH1 0x3
                  SSTORE
        """    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256,
                             coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('74bbccddeeff00112233445566778899aabbccddeeff600355')
        world.create_account(
            address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
            balance=100000000000000000000000,
            code=bytecode,
            nonce=0
        )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f3947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

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
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        # Add pos checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(world.get_nonce(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), 0)
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 100000000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('74bbccddeeff00112233445566778899aabbccddeeff600355'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x03)), 0xbbccddeeff00112233445566778899aabbccddeeff)
        # check outs
        self.assertEqual(returndata, unhexlify(''))
        # check logs
        logs = [Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs]
        data = rlp.encode(logs)
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test used gas
        self.assertEqual(to_constant(world.current_vm.gas), 79994)

    def test_push2(self):
        """
        Textcase taken from https://github.com/ethereum/tests
        File: push2.json
        sha256sum: dc950f609bd8f8918cf8680bbc8159029c3d2d657c6091a6dd53654901b15f91
        Code:     PUSH2 0xeeff
                  PUSH1 0x3
                  SSTORE
        """    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256,
                             coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('61eeff600355')
        world.create_account(
            address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
            balance=100000000000000000000000,
            code=bytecode,
            nonce=0
        )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f3947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

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
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        # Add pos checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(world.get_nonce(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), 0)
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 100000000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('61eeff600355'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x03)), 0xeeff)
        # check outs
        self.assertEqual(returndata, unhexlify(''))
        # check logs
        logs = [Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs]
        data = rlp.encode(logs)
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test used gas
        self.assertEqual(to_constant(world.current_vm.gas), 79994)

    def test_push17(self):
        """
        Textcase taken from https://github.com/ethereum/tests
        File: push17.json
        sha256sum: 9b0d44bdb54ac17d3a457112181dd8af54d141531bffd7a4b9002094279b1997
        Code:     PUSH17 0xff00112233445566778899aabbccddeeff
                  PUSH1 0x3
                  SSTORE
        """    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256,
                             coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('70ff00112233445566778899aabbccddeeff600355')
        world.create_account(
            address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
            balance=100000000000000000000000,
            code=bytecode,
            nonce=0
        )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f3947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

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
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        # Add pos checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(world.get_nonce(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), 0)
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 100000000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('70ff00112233445566778899aabbccddeeff600355'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x03)), 0xff00112233445566778899aabbccddeeff)
        # check outs
        self.assertEqual(returndata, unhexlify(''))
        # check logs
        logs = [Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs]
        data = rlp.encode(logs)
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test used gas
        self.assertEqual(to_constant(world.current_vm.gas), 79994)

    def test_dup7(self):
        """
        Textcase taken from https://github.com/ethereum/tests
        File: dup7.json
        sha256sum: c0c90a8d3ea5f5311b23de61732ff543f3b01e2054125ddadb3533d85e69793d
        Code:     PUSH1 0x7
                  PUSH1 0x6
                  PUSH1 0x5
                  PUSH1 0x4
                  PUSH1 0x3
                  PUSH1 0x2
                  PUSH1 0x1
                  DUP7
                  PUSH1 0x3
                  SSTORE
        """    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256,
                             coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('600760066005600460036002600186600355')
        world.create_account(
            address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
            balance=100000000000000000000000,
            code=bytecode,
            nonce=0
        )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f3947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

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
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        # Add pos checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(world.get_nonce(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), 0)
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 100000000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('600760066005600460036002600186600355'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x03)), 0x07)
        # check outs
        self.assertEqual(returndata, unhexlify(''))
        # check logs
        logs = [Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs]
        data = rlp.encode(logs)
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test used gas
        self.assertEqual(to_constant(world.current_vm.gas), 79973)

    def test_push32FillUpInputWithZerosAtTheEnd(self):
        """
        Textcase taken from https://github.com/ethereum/tests
        File: push32FillUpInputWithZerosAtTheEnd.json
        sha256sum: 275e3e6817b9d5105ee52895f346e1b53c916d0b44f4c33af57f78e327a40649
        Code:     
        """    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256,
                             coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('7fff10112233445566778899aabbccddeeff00112233445566778899aabbccdd')
        world.create_account(
            address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
            balance=100000000000000000000000,
            code=bytecode,
            nonce=0
        )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f3947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

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
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        # Add pos checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(world.get_nonce(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), 0)
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 100000000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('7fff10112233445566778899aabbccddeeff00112233445566778899aabbccdd'))
        # check outs
        self.assertEqual(returndata, unhexlify(''))
        # check logs
        logs = [Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs]
        data = rlp.encode(logs)
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test used gas
        self.assertEqual(to_constant(world.current_vm.gas), 99997)

    def test_dup6(self):
        """
        Textcase taken from https://github.com/ethereum/tests
        File: dup6.json
        sha256sum: b3f1f261d9e25af28a4a149ce7801cdba5b172280c32016292e3f5493012b7a5
        Code:     PUSH1 0x6
                  PUSH1 0x5
                  PUSH1 0x4
                  PUSH1 0x3
                  PUSH1 0x2
                  PUSH1 0x1
                  DUP6
                  PUSH1 0x3
                  SSTORE
        """    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256,
                             coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('60066005600460036002600185600355')
        world.create_account(
            address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
            balance=100000000000000000000000,
            code=bytecode,
            nonce=0
        )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f3947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

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
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        # Add pos checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(world.get_nonce(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), 0)
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 100000000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('60066005600460036002600185600355'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x03)), 0x06)
        # check outs
        self.assertEqual(returndata, unhexlify(''))
        # check logs
        logs = [Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs]
        data = rlp.encode(logs)
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test used gas
        self.assertEqual(to_constant(world.current_vm.gas), 79976)

    def test_push16(self):
        """
        Textcase taken from https://github.com/ethereum/tests
        File: push16.json
        sha256sum: ab2a8af94128a48039ec78299145ba7c3e3473a1f61c4675d4076ed16ba73eba
        Code:     PUSH16 0x10112233445566778899aabbccddeeff
                  PUSH1 0x3
                  SSTORE
        """    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256,
                             coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('6f10112233445566778899aabbccddeeff600355')
        world.create_account(
            address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
            balance=100000000000000000000000,
            code=bytecode,
            nonce=0
        )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f3947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

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
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        # Add pos checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(world.get_nonce(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), 0)
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 100000000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('6f10112233445566778899aabbccddeeff600355'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x03)), 0x10112233445566778899aabbccddeeff)
        # check outs
        self.assertEqual(returndata, unhexlify(''))
        # check logs
        logs = [Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs]
        data = rlp.encode(logs)
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test used gas
        self.assertEqual(to_constant(world.current_vm.gas), 79994)

    def test_push3(self):
        """
        Textcase taken from https://github.com/ethereum/tests
        File: push3.json
        sha256sum: b80fe0d795d6bb989ab2910da3078774dc049ea222ed5a5ab22460a845e22f76
        Code:     PUSH3 0xddeeff
                  PUSH1 0x3
                  SSTORE
        """    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256,
                             coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('62ddeeff600355')
        world.create_account(
            address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
            balance=100000000000000000000000,
            code=bytecode,
            nonce=0
        )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f3947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

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
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        # Add pos checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(world.get_nonce(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), 0)
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 100000000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('62ddeeff600355'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x03)), 0xddeeff)
        # check outs
        self.assertEqual(returndata, unhexlify(''))
        # check logs
        logs = [Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs]
        data = rlp.encode(logs)
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test used gas
        self.assertEqual(to_constant(world.current_vm.gas), 79994)

    def test_dup16(self):
        """
        Textcase taken from https://github.com/ethereum/tests
        File: dup16.json
        sha256sum: d119ce06f81c7b094a25e000ed80e8a4fb93a3003fe51fd1b01b7337d11706df
        Code:     PUSH1 0x10
                  PUSH1 0xf
                  PUSH1 0xe
                  PUSH1 0xd
                  PUSH1 0xc
                  PUSH1 0xb
                  PUSH1 0xa
                  PUSH1 0x9
                  PUSH1 0x8
                  PUSH1 0x7
                  PUSH1 0x6
                  PUSH1 0x5
                  PUSH1 0x4
                  PUSH1 0x3
                  PUSH1 0x2
                  PUSH1 0x1
                  DUP16
                  PUSH1 0x3
                  SSTORE
        """    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256,
                             coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('6010600f600e600d600c600b600a6009600860076006600560046003600260018f600355')
        world.create_account(
            address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
            balance=100000000000000000000000,
            code=bytecode,
            nonce=0
        )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f3947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

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
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        # Add pos checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(world.get_nonce(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), 0)
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 100000000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('6010600f600e600d600c600b600a6009600860076006600560046003600260018f600355'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x03)), 0x10)
        # check outs
        self.assertEqual(returndata, unhexlify(''))
        # check logs
        logs = [Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs]
        data = rlp.encode(logs)
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test used gas
        self.assertEqual(to_constant(world.current_vm.gas), 79946)

    def test_swap1(self):
        """
        Textcase taken from https://github.com/ethereum/tests
        File: swap1.json
        sha256sum: 53e0b95222d1a72cbc76723d2e86b274ce2d783c7539c5075f7366dc7cb6f81c
        Code:     PUSH32 0x10112233445566778899aabbccddeeff00112233445566778899aabbccddeeff
                  PUSH1 0x3
                  SWAP1
                  SSTORE
        """    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256,
                             coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('7f10112233445566778899aabbccddeeff00112233445566778899aabbccddeeff60039055')
        world.create_account(
            address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
            balance=100000000000000000000000,
            code=bytecode,
            nonce=0
        )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f3947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

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
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        # Add pos checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(world.get_nonce(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), 0)
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 100000000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('7f10112233445566778899aabbccddeeff00112233445566778899aabbccddeeff60039055'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x10112233445566778899aabbccddeeff00112233445566778899aabbccddeeff)), 0x03)
        # check outs
        self.assertEqual(returndata, unhexlify(''))
        # check logs
        logs = [Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs]
        data = rlp.encode(logs)
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test used gas
        self.assertEqual(to_constant(world.current_vm.gas), 79991)

    def test_push32Undefined(self):
        """
        Textcase taken from https://github.com/ethereum/tests
        File: push32Undefined.json
        sha256sum: b8c65e9991d99a9f16441629773a994d3a859d715fc06337b87e63b630390e12
        Code:     
        """    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256,
                             coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('7f010203600055')
        world.create_account(
            address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
            balance=100000000000000000000000,
            code=bytecode,
            nonce=0
        )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f3947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

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
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        # Add pos checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(world.get_nonce(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), 0)
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 100000000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('7f010203600055'))
        # check outs
        self.assertEqual(returndata, unhexlify(''))
        # check logs
        logs = [Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs]
        data = rlp.encode(logs)
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test used gas
        self.assertEqual(to_constant(world.current_vm.gas), 99997)

    def test_push20(self):
        """
        Textcase taken from https://github.com/ethereum/tests
        File: push20.json
        sha256sum: 89a8451f45f50b9bf3aae32ca99d07ea7bdd3028696bafc4d904a808528f5e1c
        Code:     PUSH20 0xccddeeff00112233445566778899aabbccddeeff
                  PUSH1 0x3
                  SSTORE
        """    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256,
                             coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('73ccddeeff00112233445566778899aabbccddeeff600355')
        world.create_account(
            address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
            balance=100000000000000000000000,
            code=bytecode,
            nonce=0
        )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f3947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

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
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        # Add pos checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(world.get_nonce(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), 0)
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 100000000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('73ccddeeff00112233445566778899aabbccddeeff600355'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x03)), 0xccddeeff00112233445566778899aabbccddeeff)
        # check outs
        self.assertEqual(returndata, unhexlify(''))
        # check logs
        logs = [Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs]
        data = rlp.encode(logs)
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test used gas
        self.assertEqual(to_constant(world.current_vm.gas), 79994)

    def test_swap15(self):
        """
        Textcase taken from https://github.com/ethereum/tests
        File: swap15.json
        sha256sum: aea710e4c4f9e839e4da8c37d8a72bdf73f776fafa4c726274ea17a3f4766c58
        Code:     PUSH1 0xf
                  PUSH1 0xe
                  PUSH1 0xd
                  PUSH1 0xc
                  PUSH1 0xb
                  PUSH1 0xa
                  PUSH1 0x9
                  PUSH1 0x8
                  PUSH1 0x7
                  PUSH1 0x6
                  PUSH1 0x5
                  PUSH1 0x4
                  PUSH1 0x3
                  PUSH1 0x2
                  PUSH1 0x1
                  PUSH1 0x3
                  SWAP15
                  SSTORE
        """    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256,
                             coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('600f600e600d600c600b600a60096008600760066005600460036002600160039e55')
        world.create_account(
            address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
            balance=100000000000000000000000,
            code=bytecode,
            nonce=0
        )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f3947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

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
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        # Add pos checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(world.get_nonce(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), 0)
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 100000000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('600f600e600d600c600b600a60096008600760066005600460036002600160039e55'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x0f)), 0x01)
        # check outs
        self.assertEqual(returndata, unhexlify(''))
        # check logs
        logs = [Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs]
        data = rlp.encode(logs)
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test used gas
        self.assertEqual(to_constant(world.current_vm.gas), 79949)

    def test_swap6(self):
        """
        Textcase taken from https://github.com/ethereum/tests
        File: swap6.json
        sha256sum: 1a2eddde9f58a4c76a8ff220ddf0f991993d8bcfe9dfd65e88f6786714fdc85d
        Code:     PUSH1 0x6
                  PUSH1 0x5
                  PUSH1 0x4
                  PUSH1 0x3
                  PUSH1 0x2
                  PUSH1 0x1
                  PUSH1 0x3
                  SWAP6
                  SSTORE
        """    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256,
                             coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('60066005600460036002600160039555')
        world.create_account(
            address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
            balance=100000000000000000000000,
            code=bytecode,
            nonce=0
        )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f3947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

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
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        # Add pos checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(world.get_nonce(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), 0)
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 100000000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('60066005600460036002600160039555'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x06)), 0x01)
        # check outs
        self.assertEqual(returndata, unhexlify(''))
        # check logs
        logs = [Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs]
        data = rlp.encode(logs)
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test used gas
        self.assertEqual(to_constant(world.current_vm.gas), 79976)

    def test_dup11(self):
        """
        Textcase taken from https://github.com/ethereum/tests
        File: dup11.json
        sha256sum: 08ef62448878134082fba860f6870df07e4bfb10ab86d4335591dc6f1acca24d
        Code:     PUSH1 0xb
                  PUSH1 0xa
                  PUSH1 0x9
                  PUSH1 0x8
                  PUSH1 0x7
                  PUSH1 0x6
                  PUSH1 0x5
                  PUSH1 0x4
                  PUSH1 0x3
                  PUSH1 0x2
                  PUSH1 0x1
                  DUP11
                  PUSH1 0x3
                  SSTORE
        """    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256,
                             coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('600b600a6009600860076006600560046003600260018a600355')
        world.create_account(
            address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
            balance=100000000000000000000000,
            code=bytecode,
            nonce=0
        )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f3947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

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
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        # Add pos checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(world.get_nonce(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), 0)
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 100000000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('600b600a6009600860076006600560046003600260018a600355'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x03)), 0x0b)
        # check outs
        self.assertEqual(returndata, unhexlify(''))
        # check logs
        logs = [Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs]
        data = rlp.encode(logs)
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test used gas
        self.assertEqual(to_constant(world.current_vm.gas), 79961)

    def test_push4(self):
        """
        Textcase taken from https://github.com/ethereum/tests
        File: push4.json
        sha256sum: 3730fe1c565f2fc7968bd28fd7c445fc7fe9fdbc254fe7b4da3c81455366c9b7
        Code:     PUSH4 0xccddeeff
                  PUSH1 0x3
                  SSTORE
        """    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256,
                             coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('63ccddeeff600355')
        world.create_account(
            address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
            balance=100000000000000000000000,
            code=bytecode,
            nonce=0
        )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f3947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

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
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        # Add pos checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(world.get_nonce(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), 0)
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 100000000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('63ccddeeff600355'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x03)), 0xccddeeff)
        # check outs
        self.assertEqual(returndata, unhexlify(''))
        # check logs
        logs = [Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs]
        data = rlp.encode(logs)
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test used gas
        self.assertEqual(to_constant(world.current_vm.gas), 79994)

    def test_push11(self):
        """
        Textcase taken from https://github.com/ethereum/tests
        File: push11.json
        sha256sum: 0640747360174ae7934ff30c03cb028e8f16675d669d617fbf41440badc7e201
        Code:     PUSH11 0x5566778899aabbccddeeff
                  PUSH1 0x3
                  SSTORE
        """    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256,
                             coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('6a5566778899aabbccddeeff600355')
        world.create_account(
            address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
            balance=100000000000000000000000,
            code=bytecode,
            nonce=0
        )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f3947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

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
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        # Add pos checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(world.get_nonce(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), 0)
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 100000000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('6a5566778899aabbccddeeff600355'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x03)), 0x5566778899aabbccddeeff)
        # check outs
        self.assertEqual(returndata, unhexlify(''))
        # check logs
        logs = [Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs]
        data = rlp.encode(logs)
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test used gas
        self.assertEqual(to_constant(world.current_vm.gas), 79994)

    def test_dup2error(self):
        """
        Textcase taken from https://github.com/ethereum/tests
        File: dup2error.json
        sha256sum: b9772850cf546e6f05c7fb5e216dd267798710fbb1dfe1933a936dff283e0590
        Code:     PUSH32 0x10112233445566778899aabbccddeeff00112233445566778899aabbccddeeff
                  DUP2
                  PUSH1 0x3
                  SSTORE
        """    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256,
                             coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('7f10112233445566778899aabbccddeeff00112233445566778899aabbccddeeff81600355')
        world.create_account(
            address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
            balance=100000000000000000000000,
            code=bytecode,
            nonce=0
        )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f3947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

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
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #If test end in exception check it here
        self.assertTrue(result == 'THROW')

    def test_dup1(self):
        """
        Textcase taken from https://github.com/ethereum/tests
        File: dup1.json
        sha256sum: f5d5f64e266f82b8edde04699a90ffea46bf376154b4265f8a3799cbf17da134
        Code:     PUSH32 0x10112233445566778899aabbccddeeff00112233445566778899aabbccddeeff
                  DUP1
                  PUSH1 0x3
                  SSTORE
        """    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256,
                             coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('7f10112233445566778899aabbccddeeff00112233445566778899aabbccddeeff80600355')
        world.create_account(
            address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
            balance=100000000000000000000000,
            code=bytecode,
            nonce=0
        )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f3947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

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
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        # Add pos checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(world.get_nonce(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), 0)
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 100000000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('7f10112233445566778899aabbccddeeff00112233445566778899aabbccddeeff80600355'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x03)), 0x10112233445566778899aabbccddeeff00112233445566778899aabbccddeeff)
        # check outs
        self.assertEqual(returndata, unhexlify(''))
        # check logs
        logs = [Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs]
        data = rlp.encode(logs)
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test used gas
        self.assertEqual(to_constant(world.current_vm.gas), 79991)

    def test_swap12(self):
        """
        Textcase taken from https://github.com/ethereum/tests
        File: swap12.json
        sha256sum: abb7c3b6a98cff5d61ea19e0c7a2a8cdcddc2bdf89909fd17546e810b41e1024
        Code:     PUSH1 0xc
                  PUSH1 0xb
                  PUSH1 0xa
                  PUSH1 0x9
                  PUSH1 0x8
                  PUSH1 0x7
                  PUSH1 0x6
                  PUSH1 0x5
                  PUSH1 0x4
                  PUSH1 0x3
                  PUSH1 0x2
                  PUSH1 0x1
                  PUSH1 0x3
                  SWAP12
                  SSTORE
        """    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256,
                             coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('600c600b600a60096008600760066005600460036002600160039b55')
        world.create_account(
            address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
            balance=100000000000000000000000,
            code=bytecode,
            nonce=0
        )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f3947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

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
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        # Add pos checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(world.get_nonce(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), 0)
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 100000000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('600c600b600a60096008600760066005600460036002600160039b55'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x0c)), 0x01)
        # check outs
        self.assertEqual(returndata, unhexlify(''))
        # check logs
        logs = [Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs]
        data = rlp.encode(logs)
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test used gas
        self.assertEqual(to_constant(world.current_vm.gas), 79958)

    def test_push27(self):
        """
        Textcase taken from https://github.com/ethereum/tests
        File: push27.json
        sha256sum: 9254607c1500fcb2f3805b7a015a40f35e5ddb2eff66e6f1d7b976fdc97518da
        Code:     PUSH27 0x5566778899aabbccddeeff00112233445566778899aabbccddeeff
                  PUSH1 0x3
                  SSTORE
        """    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256,
                             coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('7a5566778899aabbccddeeff00112233445566778899aabbccddeeff600355')
        world.create_account(
            address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
            balance=100000000000000000000000,
            code=bytecode,
            nonce=0
        )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f3947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

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
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        # Add pos checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(world.get_nonce(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), 0)
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 100000000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('7a5566778899aabbccddeeff00112233445566778899aabbccddeeff600355'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x03)), 0x5566778899aabbccddeeff00112233445566778899aabbccddeeff)
        # check outs
        self.assertEqual(returndata, unhexlify(''))
        # check logs
        logs = [Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs]
        data = rlp.encode(logs)
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test used gas
        self.assertEqual(to_constant(world.current_vm.gas), 79994)

    def test_push31(self):
        """
        Textcase taken from https://github.com/ethereum/tests
        File: push31.json
        sha256sum: a319d2c7a3a8a33f4535a1f7fe030b23c61f8ef87f72532c83a5313fe3f1fe81
        Code:     PUSH31 0x112233445566778899aabbccddeeff00112233445566778899aabbccddeeff
                  PUSH1 0x3
                  SSTORE
        """    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256,
                             coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('7e112233445566778899aabbccddeeff00112233445566778899aabbccddeeff600355')
        world.create_account(
            address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
            balance=100000000000000000000000,
            code=bytecode,
            nonce=0
        )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f3947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

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
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        # Add pos checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(world.get_nonce(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), 0)
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 100000000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('7e112233445566778899aabbccddeeff00112233445566778899aabbccddeeff600355'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x03)), 0x112233445566778899aabbccddeeff00112233445566778899aabbccddeeff)
        # check outs
        self.assertEqual(returndata, unhexlify(''))
        # check logs
        logs = [Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs]
        data = rlp.encode(logs)
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test used gas
        self.assertEqual(to_constant(world.current_vm.gas), 79994)

    def test_push8(self):
        """
        Textcase taken from https://github.com/ethereum/tests
        File: push8.json
        sha256sum: 9e04bd942a06762fd2f1142953591a8ff58c17160c6c9a86b43ff0d8efed3234
        Code:     PUSH8 0x8899aabbccddeeff
                  PUSH1 0x3
                  SSTORE
        """    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256,
                             coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('678899aabbccddeeff600355')
        world.create_account(
            address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
            balance=100000000000000000000000,
            code=bytecode,
            nonce=0
        )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f3947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

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
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        # Add pos checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(world.get_nonce(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), 0)
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 100000000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('678899aabbccddeeff600355'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x03)), 0x8899aabbccddeeff)
        # check outs
        self.assertEqual(returndata, unhexlify(''))
        # check logs
        logs = [Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs]
        data = rlp.encode(logs)
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test used gas
        self.assertEqual(to_constant(world.current_vm.gas), 79994)

    def test_push9(self):
        """
        Textcase taken from https://github.com/ethereum/tests
        File: push9.json
        sha256sum: 30d5fedfa182e11f5e93e9ec590a32d3a4d8cf9ead1c6ab8bfdef32b00d656f0
        Code:     PUSH9 0x778899aabbccddeeff
                  PUSH1 0x3
                  SSTORE
        """    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256,
                             coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('68778899aabbccddeeff600355')
        world.create_account(
            address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
            balance=100000000000000000000000,
            code=bytecode,
            nonce=0
        )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f3947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

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
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        # Add pos checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(world.get_nonce(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), 0)
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 100000000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('68778899aabbccddeeff600355'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x03)), 0x778899aabbccddeeff)
        # check outs
        self.assertEqual(returndata, unhexlify(''))
        # check logs
        logs = [Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs]
        data = rlp.encode(logs)
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test used gas
        self.assertEqual(to_constant(world.current_vm.gas), 79994)

    def test_push30(self):
        """
        Textcase taken from https://github.com/ethereum/tests
        File: push30.json
        sha256sum: b578e55fec71726ca9c72940ce5d1e84c0bdb9cd8e36d2265f8392238d12294d
        Code:     PUSH30 0x2233445566778899aabbccddeeff00112233445566778899aabbccddeeff
                  PUSH1 0x3
                  SSTORE
        """    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256,
                             coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('7d2233445566778899aabbccddeeff00112233445566778899aabbccddeeff600355')
        world.create_account(
            address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
            balance=100000000000000000000000,
            code=bytecode,
            nonce=0
        )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f3947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

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
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        # Add pos checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(world.get_nonce(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), 0)
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 100000000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('7d2233445566778899aabbccddeeff00112233445566778899aabbccddeeff600355'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x03)), 0x2233445566778899aabbccddeeff00112233445566778899aabbccddeeff)
        # check outs
        self.assertEqual(returndata, unhexlify(''))
        # check logs
        logs = [Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs]
        data = rlp.encode(logs)
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test used gas
        self.assertEqual(to_constant(world.current_vm.gas), 79994)

    def test_push26(self):
        """
        Textcase taken from https://github.com/ethereum/tests
        File: push26.json
        sha256sum: b553759fd07ebc6fbf534ab7ccc341a63ba29e41848732de82a2fd7f692ad5aa
        Code:     PUSH26 0x66778899aabbccddeeff00112233445566778899aabbccddeeff
                  PUSH1 0x3
                  SSTORE
        """    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256,
                             coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('7966778899aabbccddeeff00112233445566778899aabbccddeeff600355')
        world.create_account(
            address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
            balance=100000000000000000000000,
            code=bytecode,
            nonce=0
        )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f3947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

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
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        # Add pos checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(world.get_nonce(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), 0)
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 100000000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('7966778899aabbccddeeff00112233445566778899aabbccddeeff600355'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x03)), 0x66778899aabbccddeeff00112233445566778899aabbccddeeff)
        # check outs
        self.assertEqual(returndata, unhexlify(''))
        # check logs
        logs = [Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs]
        data = rlp.encode(logs)
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test used gas
        self.assertEqual(to_constant(world.current_vm.gas), 79994)

    def test_swap13(self):
        """
        Textcase taken from https://github.com/ethereum/tests
        File: swap13.json
        sha256sum: 1ebf245754471dd288faca601efde5b3b26904830cb1c080539b856923a4cf53
        Code:     PUSH1 0xd
                  PUSH1 0xc
                  PUSH1 0xb
                  PUSH1 0xa
                  PUSH1 0x9
                  PUSH1 0x8
                  PUSH1 0x7
                  PUSH1 0x6
                  PUSH1 0x5
                  PUSH1 0x4
                  PUSH1 0x3
                  PUSH1 0x2
                  PUSH1 0x1
                  PUSH1 0x3
                  SWAP13
                  SSTORE
        """    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256,
                             coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('600d600c600b600a60096008600760066005600460036002600160039c55')
        world.create_account(
            address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
            balance=100000000000000000000000,
            code=bytecode,
            nonce=0
        )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f3947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

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
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        # Add pos checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(world.get_nonce(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), 0)
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 100000000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('600d600c600b600a60096008600760066005600460036002600160039c55'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x0d)), 0x01)
        # check outs
        self.assertEqual(returndata, unhexlify(''))
        # check logs
        logs = [Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs]
        data = rlp.encode(logs)
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test used gas
        self.assertEqual(to_constant(world.current_vm.gas), 79955)

    def test_push10(self):
        """
        Textcase taken from https://github.com/ethereum/tests
        File: push10.json
        sha256sum: d27ece2fa104c2008f94827a903324641882e6c77ed848896df83286979cdb0f
        Code:     PUSH10 0x66778899aabbccddeeff
                  PUSH1 0x3
                  SSTORE
        """    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256,
                             coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('6966778899aabbccddeeff600355')
        world.create_account(
            address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
            balance=100000000000000000000000,
            code=bytecode,
            nonce=0
        )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f3947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

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
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        # Add pos checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(world.get_nonce(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), 0)
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 100000000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('6966778899aabbccddeeff600355'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x03)), 0x66778899aabbccddeeff)
        # check outs
        self.assertEqual(returndata, unhexlify(''))
        # check logs
        logs = [Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs]
        data = rlp.encode(logs)
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test used gas
        self.assertEqual(to_constant(world.current_vm.gas), 79994)

    def test_push5(self):
        """
        Textcase taken from https://github.com/ethereum/tests
        File: push5.json
        sha256sum: 708610919b1dd3bf7dda2474eafa0eeeb7024f04b11663f01973e112834ddbdb
        Code:     PUSH5 0xbbccddeeff
                  PUSH1 0x3
                  SSTORE
        """    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256,
                             coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('64bbccddeeff600355')
        world.create_account(
            address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
            balance=100000000000000000000000,
            code=bytecode,
            nonce=0
        )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f3947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

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
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        # Add pos checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(world.get_nonce(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), 0)
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 100000000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('64bbccddeeff600355'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x03)), 0xbbccddeeff)
        # check outs
        self.assertEqual(returndata, unhexlify(''))
        # check logs
        logs = [Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs]
        data = rlp.encode(logs)
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test used gas
        self.assertEqual(to_constant(world.current_vm.gas), 79994)

    def test_swap7(self):
        """
        Textcase taken from https://github.com/ethereum/tests
        File: swap7.json
        sha256sum: 0c017d4cf7588fafc71237fc2fbce73741e6da63e6f604158c2d9477d3adcb47
        Code:     PUSH1 0x7
                  PUSH1 0x6
                  PUSH1 0x5
                  PUSH1 0x4
                  PUSH1 0x3
                  PUSH1 0x2
                  PUSH1 0x1
                  PUSH1 0x3
                  SWAP7
                  SSTORE
        """    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256,
                             coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('600760066005600460036002600160039655')
        world.create_account(
            address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
            balance=100000000000000000000000,
            code=bytecode,
            nonce=0
        )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f3947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

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
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        # Add pos checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(world.get_nonce(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), 0)
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 100000000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('600760066005600460036002600160039655'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x07)), 0x01)
        # check outs
        self.assertEqual(returndata, unhexlify(''))
        # check logs
        logs = [Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs]
        data = rlp.encode(logs)
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test used gas
        self.assertEqual(to_constant(world.current_vm.gas), 79973)

    def test_dup10(self):
        """
        Textcase taken from https://github.com/ethereum/tests
        File: dup10.json
        sha256sum: 6df95c92e21fec233820d1b4b4c25e660708c18e90c3e28a2424aedbc6aad4ef
        Code:     PUSH1 0xa
                  PUSH1 0x9
                  PUSH1 0x8
                  PUSH1 0x7
                  PUSH1 0x6
                  PUSH1 0x5
                  PUSH1 0x4
                  PUSH1 0x3
                  PUSH1 0x2
                  PUSH1 0x1
                  DUP10
                  PUSH1 0x3
                  SSTORE
        """    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256,
                             coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('600a60096008600760066005600460036002600189600355')
        world.create_account(
            address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
            balance=100000000000000000000000,
            code=bytecode,
            nonce=0
        )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f3947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

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
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        # Add pos checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(world.get_nonce(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), 0)
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 100000000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('600a60096008600760066005600460036002600189600355'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x03)), 0x0a)
        # check outs
        self.assertEqual(returndata, unhexlify(''))
        # check logs
        logs = [Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs]
        data = rlp.encode(logs)
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test used gas
        self.assertEqual(to_constant(world.current_vm.gas), 79964)

    def test_push1_missingStack(self):
        """
        Textcase taken from https://github.com/ethereum/tests
        File: push1_missingStack.json
        sha256sum: 83b63953c825b5488709da1d4e74cc1230eb561867fd1a21fb42471e63e99af0
        Code:     
        """    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256,
                             coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('60')
        world.create_account(
            address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
            balance=100000000000000000000000,
            code=bytecode,
            nonce=0
        )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f3947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

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
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        # Add pos checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        # check nonce, balance, code
        self.assertEqual(world.get_nonce(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), 0)
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 100000000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('60'))
        # check outs
        self.assertEqual(returndata, unhexlify(''))
        # check logs
        logs = [Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs]
        data = rlp.encode(logs)
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test used gas
        self.assertEqual(to_constant(world.current_vm.gas), 99997)


if __name__ == '__main__':
    unittest.main()
