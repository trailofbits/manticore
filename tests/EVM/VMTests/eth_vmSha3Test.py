
#Taken from /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmSha3Test
import struct
import unittest
import json
import os
from binascii import unhexlify
from manticore.platforms import evm
from manticore.core import state
from manticore.core.smtlib import Operators, ConstraintSet
from manticore.core.smtlib.visitors import to_constant
import sha3
import rlp
from rlp.sedes import (
    CountableList,
    BigEndianInt,
    Binary,
)
class Log(rlp.Serializable):
    fields = [
        ('address', Binary.fixed_length(20, allow_empty=True)),
        ('topics', CountableList(BigEndianInt(32))),
        ('data', Binary())
    ]

class EVMTest_vmSha3Test(unittest.TestCase):
    _multiprocess_can_split_ = True
    maxDiff=None 


    def test_sha3_memSizeQuadraticCost64_2(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmSha3Test/sha3_memSizeQuadraticCost64_2.json
            sha256sum: 484b0804d4aec5fd813f4fde615c193764a559f9782ccc3e9c38197bebbd6d2a
            Code: PUSH1 0x20
                  PUSH2 0x7e0
                  SHA3
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('60206107e020600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=115792089237316195423570985008687907853269984665640564039457584007913129639935,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x1
        data = ''
        caller = 0xcd1722f3947def4cf144679da39c4c32bdc35681
        value = 115792089237316195423570985008687907853269984665640564039457584007913129639935
        gas = 4294967296

        # open a fake tx, no funds send
        world._open_transaction('CALL', address, price, data, caller, value, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                world.current_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce, balance, code
        self.assertEqual(world.get_nonce(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), 0)
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 115792089237316195423570985008687907853269984665640564039457584007913129639935)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('60206107e020600055'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0x290decd9548b62a8d60345a988386fc84ba6bc95484008f6362f93160ef3e563)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 4294947051)

    def test_sha3_6(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmSha3Test/sha3_6.json
            sha256sum: e0e919385169dc814ac196f2004f0e8b98ca3b638ed0692f8fbf606ac8221a56
            Code: PUSH32 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
                  PUSH32 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
                  SHA3
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff20600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
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

        result = None
        returndata = b''
        try:
            while True:
                world.current_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #If test end in exception ceck it here
        self.assertTrue(result in ('THROW'))

    def test_sha3_0(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmSha3Test/sha3_0.json
            sha256sum: a0400c8194bdd7aa5867b90c0c042bafc36a97169c2443788a767b7808413415
            Code: PUSH1 0x0
                  PUSH1 0x0
                  SHA3
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('6000600020600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=100000000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x3b9aca00
        data = ''
        caller = 0xcd1722f3947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000000000

        # open a fake tx, no funds send
        world._open_transaction('CALL', address, price, data, caller, value, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                world.current_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce, balance, code
        self.assertEqual(world.get_nonce(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), 0)
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 100000000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('6000600020600055'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0xc5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 99999979961)

    def test_sha3_memSizeQuadraticCost32_zeroSize(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmSha3Test/sha3_memSizeQuadraticCost32_zeroSize.json
            sha256sum: 87486b55c820d44fd3871303fa7a1dd31373cdbb7380d4dfd62e41b7e400827c
            Code: PUSH1 0x0
                  PUSH2 0x400
                  SHA3
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('600061040020600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=115792089237316195423570985008687907853269984665640564039457584007913129639935,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x1
        data = ''
        caller = 0xcd1722f3947def4cf144679da39c4c32bdc35681
        value = 115792089237316195423570985008687907853269984665640564039457584007913129639935
        gas = 4294967296

        # open a fake tx, no funds send
        world._open_transaction('CALL', address, price, data, caller, value, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                world.current_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce, balance, code
        self.assertEqual(world.get_nonce(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), 0)
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 115792089237316195423570985008687907853269984665640564039457584007913129639935)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('600061040020600055'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0xc5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 4294947257)

    def test_sha3_memSizeQuadraticCost32(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmSha3Test/sha3_memSizeQuadraticCost32.json
            sha256sum: 3fdb5fd400ad47fc4cc3e2776edd7a8f7fb430710b7bd43832a395069dc0912e
            Code: PUSH1 0x1
                  PUSH2 0x3e0
                  SHA3
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('60016103e020600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=115792089237316195423570985008687907853269984665640564039457584007913129639935,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x1
        data = ''
        caller = 0xcd1722f3947def4cf144679da39c4c32bdc35681
        value = 115792089237316195423570985008687907853269984665640564039457584007913129639935
        gas = 4294967296

        # open a fake tx, no funds send
        world._open_transaction('CALL', address, price, data, caller, value, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                world.current_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce, balance, code
        self.assertEqual(world.get_nonce(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), 0)
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 115792089237316195423570985008687907853269984665640564039457584007913129639935)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('60016103e020600055'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0xbc36789e7a1e281436464229828f817d6612f7b477d66591ff96a9e064bcc98a)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 4294947153)

    def test_sha3_memSizeQuadraticCost33(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmSha3Test/sha3_memSizeQuadraticCost33.json
            sha256sum: 59f3e75cd0d2c6e68d7c2433aebf261cb8576bf3a2100d49344ee40023ae66c0
            Code: PUSH1 0x1
                  PUSH2 0x400
                  SHA3
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('600161040020600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=115792089237316195423570985008687907853269984665640564039457584007913129639935,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x1
        data = ''
        caller = 0xcd1722f3947def4cf144679da39c4c32bdc35681
        value = 115792089237316195423570985008687907853269984665640564039457584007913129639935
        gas = 4294967296

        # open a fake tx, no funds send
        world._open_transaction('CALL', address, price, data, caller, value, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                world.current_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce, balance, code
        self.assertEqual(world.get_nonce(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), 0)
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 115792089237316195423570985008687907853269984665640564039457584007913129639935)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('600161040020600055'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0xbc36789e7a1e281436464229828f817d6612f7b477d66591ff96a9e064bcc98a)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 4294947150)

    def test_sha3_memSizeQuadraticCost65(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmSha3Test/sha3_memSizeQuadraticCost65.json
            sha256sum: c165d705bc58265dbba001d94b0bb5bbe75666e2783493e64f7c1ead456b5e90
            Code: PUSH1 0x1
                  PUSH2 0x800
                  SHA3
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('600161080020600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=115792089237316195423570985008687907853269984665640564039457584007913129639935,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x1
        data = ''
        caller = 0xcd1722f3947def4cf144679da39c4c32bdc35681
        value = 115792089237316195423570985008687907853269984665640564039457584007913129639935
        gas = 4294967296

        # open a fake tx, no funds send
        world._open_transaction('CALL', address, price, data, caller, value, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                world.current_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce, balance, code
        self.assertEqual(world.get_nonce(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), 0)
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 115792089237316195423570985008687907853269984665640564039457584007913129639935)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('600161080020600055'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0xbc36789e7a1e281436464229828f817d6612f7b477d66591ff96a9e064bcc98a)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 4294947048)

    def test_sha3_memSizeNoQuadraticCost31(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmSha3Test/sha3_memSizeNoQuadraticCost31.json
            sha256sum: 906fcfb709ea8c608c6fd6e6888ae6d560b85bb180dcf56717326909f10e04f6
            Code: PUSH1 0x1
                  PUSH2 0x3c0
                  SHA3
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('60016103c020600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=115792089237316195423570985008687907853269984665640564039457584007913129639935,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x1
        data = ''
        caller = 0xcd1722f3947def4cf144679da39c4c32bdc35681
        value = 115792089237316195423570985008687907853269984665640564039457584007913129639935
        gas = 4294967296

        # open a fake tx, no funds send
        world._open_transaction('CALL', address, price, data, caller, value, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                world.current_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce, balance, code
        self.assertEqual(world.get_nonce(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), 0)
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 115792089237316195423570985008687907853269984665640564039457584007913129639935)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('60016103c020600055'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0xbc36789e7a1e281436464229828f817d6612f7b477d66591ff96a9e064bcc98a)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 4294947157)

    def test_sha3_bigSize(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmSha3Test/sha3_bigSize.json
            sha256sum: 10b138844960eca528673e19ee0f2519af7357e823482929f6853ef0bc3ef31d
            Code: PUSH31 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
                  PUSH31 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
                  SHA3
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('7effffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7effffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff20600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=115792089237316195423570985008687907853269984665640564039457584007913129639935,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x1
        data = ''
        caller = 0xcd1722f3947def4cf144679da39c4c32bdc35681
        value = 115792089237316195423570985008687907853269984665640564039457584007913129639935
        gas = 1099511627776

        # open a fake tx, no funds send
        world._open_transaction('CALL', address, price, data, caller, value, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                world.current_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #If test end in exception ceck it here
        self.assertTrue(result in ('THROW'))

    def test_sha3_4(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmSha3Test/sha3_4.json
            sha256sum: fe097ee884928a8dfcfa6a0258a18654bc032c4e0e2892ab7be68a1a27d8c2f2
            Code: PUSH1 0x64
                  PUSH5 0xfffffffff
                  SHA3
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('6064640fffffffff20600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
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

        result = None
        returndata = b''
        try:
            while True:
                world.current_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #If test end in exception ceck it here
        self.assertTrue(result in ('THROW'))

    def test_sha3_2(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmSha3Test/sha3_2.json
            sha256sum: bc2bf793089133ecd9b1321e9983c8172b931be81cbc0335455db604ce4e9ebd
            Code: PUSH1 0xa
                  PUSH1 0xa
                  SHA3
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('600a600a20600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
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

        result = None
        returndata = b''
        try:
            while True:
                world.current_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce, balance, code
        self.assertEqual(world.get_nonce(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), 0)
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 100000000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('600a600a20600055'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0x6bd2dd6bd408cbee33429358bf24fdc64612fbf8b1b4db604518f40ffd34b607)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 79952)

    def test_sha3_bigOffset2(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmSha3Test/sha3_bigOffset2.json
            sha256sum: 7a8fbc1f1d00c4b7478a491c3418fd3d863e4fbde6c999e72315b345f01d5da8
            Code: PUSH1 0x2
                  PUSH4 0x1000000
                  SHA3
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('6002630100000020600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=115792089237316195423570985008687907853269984665640564039457584007913129639935,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x1
        data = ''
        caller = 0xcd1722f3947def4cf144679da39c4c32bdc35681
        value = 115792089237316195423570985008687907853269984665640564039457584007913129639935
        gas = 4294967296

        # open a fake tx, no funds send
        world._open_transaction('CALL', address, price, data, caller, value, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                world.current_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce, balance, code
        self.assertEqual(world.get_nonce(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), 0)
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 115792089237316195423570985008687907853269984665640564039457584007913129639935)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('6002630100000020600055'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0x54a8c0ab653c15bfb48b47fd011ba2b9617af01cb45cab344acd57c924d56798)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 3756501424)

    def test_sha3_memSizeQuadraticCost64(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmSha3Test/sha3_memSizeQuadraticCost64.json
            sha256sum: cdff7625bffff36ef3cc2ed30d450654f813e43b96efd0a93ca8cbc47be2ba84
            Code: PUSH1 0x1
                  PUSH2 0x7e0
                  SHA3
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('60016107e020600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=115792089237316195423570985008687907853269984665640564039457584007913129639935,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x1
        data = ''
        caller = 0xcd1722f3947def4cf144679da39c4c32bdc35681
        value = 115792089237316195423570985008687907853269984665640564039457584007913129639935
        gas = 4294967296

        # open a fake tx, no funds send
        world._open_transaction('CALL', address, price, data, caller, value, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                world.current_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce, balance, code
        self.assertEqual(world.get_nonce(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), 0)
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 115792089237316195423570985008687907853269984665640564039457584007913129639935)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('60016107e020600055'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0xbc36789e7a1e281436464229828f817d6612f7b477d66591ff96a9e064bcc98a)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 4294947051)

    def test_sha3_memSizeQuadraticCost63(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmSha3Test/sha3_memSizeQuadraticCost63.json
            sha256sum: 290714c5e6ccd425830f67fd6cd2b5aacb8552dd78e2caf0386500cdf4c50c29
            Code: PUSH1 0x1
                  PUSH2 0x7c0
                  SHA3
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('60016107c020600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=115792089237316195423570985008687907853269984665640564039457584007913129639935,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x1
        data = ''
        caller = 0xcd1722f3947def4cf144679da39c4c32bdc35681
        value = 115792089237316195423570985008687907853269984665640564039457584007913129639935
        gas = 4294967296

        # open a fake tx, no funds send
        world._open_transaction('CALL', address, price, data, caller, value, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                world.current_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce, balance, code
        self.assertEqual(world.get_nonce(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), 0)
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 115792089237316195423570985008687907853269984665640564039457584007913129639935)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('60016107c020600055'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0xbc36789e7a1e281436464229828f817d6612f7b477d66591ff96a9e064bcc98a)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 4294947055)

    def test_sha3_1(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmSha3Test/sha3_1.json
            sha256sum: 020603b04c07deaaf3b5f2803b3208da9f296548bbef997df6b78695c4c26161
            Code: PUSH1 0x5
                  PUSH1 0x4
                  SHA3
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('6005600420600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
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

        result = None
        returndata = b''
        try:
            while True:
                world.current_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce, balance, code
        self.assertEqual(world.get_nonce(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), 0)
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 100000000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('6005600420600055'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0xc41589e7559804ea4a2080dad19d876a024ccb05117835447d72ce08c1d020ec)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 79952)

    def test_sha3_3(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmSha3Test/sha3_3.json
            sha256sum: 907dc34c33704e368b0d00ac285b3e383ba6964db07bd86cb85e65729c7d2c3c
            Code: PUSH3 0xfffff
                  PUSH2 0x3e8
                  SHA3
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('620fffff6103e820600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
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

        result = None
        returndata = b''
        try:
            while True:
                world.current_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #If test end in exception ceck it here
        self.assertTrue(result in ('THROW'))

    def test_sha3_bigOffset(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmSha3Test/sha3_bigOffset.json
            sha256sum: 14a23c7c062c1bc577a9b846df7fd49fbe7e82e89ac6b6ac3a2ceead93d201a0
            Code: PUSH1 0x2
                  PUSH31 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
                  SHA3
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('60027e0fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff20600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=115792089237316195423570985008687907853269984665640564039457584007913129639935,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x1
        data = ''
        caller = 0xcd1722f3947def4cf144679da39c4c32bdc35681
        value = 115792089237316195423570985008687907853269984665640564039457584007913129639935
        gas = 1099511627776

        # open a fake tx, no funds send
        world._open_transaction('CALL', address, price, data, caller, value, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                world.current_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #If test end in exception ceck it here
        self.assertTrue(result in ('THROW'))

    def test_sha3_5(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmSha3Test/sha3_5.json
            sha256sum: 755aebdc66bf9abe9466d3c106212a71f2f9eb5252987b9b47eed238fecb0203
            Code: PUSH5 0xfffffffff
                  PUSH2 0x2710
                  SHA3
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('640fffffffff61271020600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
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

        result = None
        returndata = b''
        try:
            while True:
                world.current_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #If test end in exception ceck it here
        self.assertTrue(result in ('THROW'))

if __name__ == '__main__':
    unittest.main()
