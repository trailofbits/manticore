
#Taken from /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmBitwiseLogicOperation
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

class EVMTest_vmBitwiseLogicOperation(unittest.TestCase):
    _multiprocess_can_split_ = True
    maxDiff=None 


    def test_byte11(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmBitwiseLogicOperation/byte11.json
            sha256sum: 36ec91353e95d67e9a504d6ba3b146cf3c1f9cd8653b4457fd3a12efebe0fb49
            Code: PUSH8 0x8040201008040201
                  PUSH1 0x0
                  BYTE
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('67804020100804020160001a600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000000000,
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('67804020100804020160001a600055'))
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 94988)

    def test_not0(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmBitwiseLogicOperation/not0.json
            sha256sum: 9a63cd9e1ee72d45d11a56bbecd60457eeb73d44bc2924ac01f324cc9d614f84
            Code: PUSH1 0x0
                  NOT
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('600019600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000000000,
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('600019600055'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 79991)

    def test_byte0(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmBitwiseLogicOperation/byte0.json
            sha256sum: 9d1905991a75b27d1646198dc171a92523cd5d652916d42bc91586714bbb7e3b
            Code: PUSH8 0x8040201008040201
                  PUSH1 0x0
                  PUSH1 0x1f
                  SUB
                  BYTE
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('6780402010080402016000601f031a600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000000000,
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('6780402010080402016000601f031a600055'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0x01)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 79982)

    def test_xor0(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmBitwiseLogicOperation/xor0.json
            sha256sum: 78cff4b175950a98f4179672a337620cc8a6940567c372bf08d8207048f6b471
            Code: PUSH1 0x2
                  PUSH1 0x2
                  XOR
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('6002600218600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000000000,
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('6002600218600055'))
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 94988)

    def test_or5(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmBitwiseLogicOperation/or5.json
            sha256sum: e420507a807b1afe85cbabbd94de1053c6f2a66f416070269a0c4e80163b87da
            Code: PUSH32 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
                  PUSH32 0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeefeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee
                  OR
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7feeeeeeeeeeeeeeeeeeeeeeeeeeeeefeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee17600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000000000,
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7feeeeeeeeeeeeeeeeeeeeeeeeeeeeefeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee17600055'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 79988)

    def test_and3(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmBitwiseLogicOperation/and3.json
            sha256sum: a1f18bb2c999f9489e9151d081d7d572e9af14a612e2ae0c4db7a2d6abd703ea
            Code: PUSH32 0x123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef
                  PUSH32 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
                  AND
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('7f0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff16600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000000000,
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('7f0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff16600055'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0x0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 79988)

    def test_iszero0(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmBitwiseLogicOperation/iszero0.json
            sha256sum: 117c6bdc9191634c764db03957c3ae105e1cfeefdb8047a81fbe7f14af2b1f42
            Code: PUSH32 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
                  ISZERO
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff15600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000000000,
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff15600055'))
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 94991)

    def test_and2(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmBitwiseLogicOperation/and2.json
            sha256sum: f04e1afac4a26cc70d2d5c7bbec57f3ae25e5d5db42d906528c8557699bc8f99
            Code: PUSH1 0x1
                  PUSH1 0x3
                  AND
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('6001600316600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000000000,
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('6001600316600055'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0x01)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 79988)

    def test_or4(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmBitwiseLogicOperation/or4.json
            sha256sum: 7cfecbc33733934671b74c6d0ae87fea68a60cacc3548f85fa1e386d0de3e625
            Code: PUSH32 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
                  PUSH32 0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee
                  OR
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7feeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee17600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000000000,
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7feeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee17600055'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 79988)

    def test_lt3(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmBitwiseLogicOperation/lt3.json
            sha256sum: 66e02544034a79b170993bdeea75a1bcb84b58354f0cf1ba4ac78d67d19a1218
            Code: PUSH32 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
                  PUSH1 0x0
                  LT
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff600010600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000000000,
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff600010600055'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0x01)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 79988)

    def test_slt0(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmBitwiseLogicOperation/slt0.json
            sha256sum: 07a690c78be0e66c314e7d168a980f82217b0a906a23f6ba56dbe4871e0e1e9e
            Code: PUSH1 0x0
                  PUSH1 0x2
                  PUSH1 0x0
                  SUB
                  SLT
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('6000600260000312600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000000000,
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('6000600260000312600055'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0x01)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 79982)

    def test_not4(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmBitwiseLogicOperation/not4.json
            sha256sum: 5e2a8dbbc0bdb52bc745204b3fc3a7d5ad9d570d0ca533a7ede7c85c8bb54726
            Code: PUSH32 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
                  PUSH1 0x0
                  SUB
                  NOT
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff60000319600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000000000,
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff60000319600055'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 79985)

    def test_sgt4(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmBitwiseLogicOperation/sgt4.json
            sha256sum: 612a50d0ddaa9dccd8662693074d0be8df98080eea196dd80f475054e744c065
            Code: PUSH1 0x3
                  PUSH1 0x0
                  SUB
                  PUSH1 0x5
                  PUSH1 0x0
                  SUB
                  SGT
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('6003600003600560000313600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000000000,
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('6003600003600560000313600055'))
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 94976)

    def test_and0(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmBitwiseLogicOperation/and0.json
            sha256sum: 7fecef8e3ae065464e168adb5cb28596ee5ee587a76bca2485e79ea7219c7434
            Code: PUSH1 0x2
                  PUSH1 0x2
                  AND
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('6002600216600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000000000,
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('6002600216600055'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0x02)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 79988)

    def test_slt3(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmBitwiseLogicOperation/slt3.json
            sha256sum: b4b3bf4d44186e07906fab6488bef6d6feba431dfce9c07136097ee248401f78
            Code: PUSH32 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
                  PUSH1 0x0
                  SLT
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff600012600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000000000,
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff600012600055'))
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 94988)

    def test_gt1(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmBitwiseLogicOperation/gt1.json
            sha256sum: 27ae257421645d7f8ae7eb0188a1a7d9d67b0b3f6f831c7db874eef5eb588a7d
            Code: PUSH1 0x2
                  PUSH1 0x0
                  SUB
                  PUSH1 0x0
                  GT
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('6002600003600011600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000000000,
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('6002600003600011600055'))
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 94982)

    def test_sgt2(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmBitwiseLogicOperation/sgt2.json
            sha256sum: 587819ebd4f68cfa226dd275e0d571c29fc3e40c38414da6c2b78b525f10b8eb
            Code: PUSH1 0x0
                  PUSH32 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
                  SGT
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('60007fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff13600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000000000,
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('60007fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff13600055'))
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 94988)

    def test_or3(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmBitwiseLogicOperation/or3.json
            sha256sum: 51eb8154aa7a75b008912838f32a0b440ed3fa95c1be9e79191739392b1f06d1
            Code: PUSH32 0x123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef
                  PUSH32 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
                  OR
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('7f0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff17600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000000000,
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('7f0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff17600055'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 79988)

    def test_eq1(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmBitwiseLogicOperation/eq1.json
            sha256sum: 803a9cf093687e3c19b98171bfa72650fadc9c0f92720a16d631a581eb94d8de
            Code: PUSH1 0x0
                  PUSH1 0x0
                  EQ
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('6000600014600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000000000,
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('6000600014600055'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0x01)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 79988)

    def test_slt1(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmBitwiseLogicOperation/slt1.json
            sha256sum: 3b8519ed73796e6b107319ead5cae650b399d3fc0307f761f7b9978d2086220a
            Code: PUSH1 0x2
                  PUSH1 0x0
                  SUB
                  PUSH1 0x0
                  SLT
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('6002600003600012600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000000000,
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('6002600003600012600055'))
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 94982)

    def test_xor3(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmBitwiseLogicOperation/xor3.json
            sha256sum: c52d020227c77418a8363eb8e61ece76717b2db6444a1331d87d38acaeb94552
            Code: PUSH32 0x123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef
                  PUSH32 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
                  XOR
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('7f0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff18600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000000000,
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('7f0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff18600055'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0xfedcba9876543210fedcba9876543210fedcba9876543210fedcba9876543210)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 79988)

    def test_or1(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmBitwiseLogicOperation/or1.json
            sha256sum: 5dcc3ed267a34d7e84692a4a947834ef806d74748a5ae875fef7d8b5b0227112
            Code: PUSH1 0x1
                  PUSH1 0x2
                  OR
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('6001600217600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000000000,
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('6001600217600055'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0x03)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 79988)

    def test_byte7(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmBitwiseLogicOperation/byte7.json
            sha256sum: e486bb059785282fd8ddb6fd7f9f73c41345b0e405e2b42018d5381e562d298b
            Code: PUSH8 0x8040201008040201
                  PUSH1 0x7
                  PUSH1 0x1f
                  SUB
                  BYTE
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('6780402010080402016007601f031a600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000000000,
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('6780402010080402016007601f031a600055'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0x80)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 79982)

    def test_or0(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmBitwiseLogicOperation/or0.json
            sha256sum: 339d36d43c3be2eb46195093bc89c42c452141f97a5373eab2c51e9b9006e03b
            Code: PUSH1 0x2
                  PUSH1 0x2
                  OR
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('6002600217600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000000000,
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('6002600217600055'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0x02)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 79988)

    def test_byte3(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmBitwiseLogicOperation/byte3.json
            sha256sum: 8eefda4db26a68718fd26d9392de7690a2861a489199eafe3499c980dee39436
            Code: PUSH8 0x8040201008040201
                  PUSH1 0x3
                  PUSH1 0x1f
                  SUB
                  BYTE
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('6780402010080402016003601f031a600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000000000,
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('6780402010080402016003601f031a600055'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0x08)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 79982)

    def test_not5(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmBitwiseLogicOperation/not5.json
            sha256sum: 61618d51c84fdf2c3bf5bf70fa975d39f66ed832bcd9493a5136814162a8c3f5
            Code: PUSH1 0x0
                  PUSH1 0x0
                  SUB
                  NOT
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('600060000319600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000000000,
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('600060000319600055'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 79985)

    def test_sgt0(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmBitwiseLogicOperation/sgt0.json
            sha256sum: 1f9ed0e3bdcd71ce340c384367ebf0bc04207e6adf5fbb4c47235721b331e1fb
            Code: PUSH1 0x0
                  PUSH1 0x2
                  PUSH1 0x0
                  SUB
                  SGT
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('6000600260000313600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000000000,
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('6000600260000313600055'))
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 94982)

    def test_byte1(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmBitwiseLogicOperation/byte1.json
            sha256sum: 6802c56441ccb9c76ff4ac6040b3285190e143c7bbe6c783608273150878bd05
            Code: PUSH8 0x8040201008040201
                  PUSH1 0x1
                  PUSH1 0x1f
                  SUB
                  BYTE
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('6780402010080402016001601f031a600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000000000,
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('6780402010080402016001601f031a600055'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0x02)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 79982)

    def test_eq0(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmBitwiseLogicOperation/eq0.json
            sha256sum: c97dffd8fd655196d1f47b800d6f2ac63f3fc01c55c898c4713eb0796b031d0a
            Code: PUSH1 0x3
                  PUSH1 0x0
                  SUB
                  PUSH1 0x5
                  PUSH1 0x0
                  SUB
                  EQ
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('6003600003600560000314600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000000000,
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('6003600003600560000314600055'))
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 94976)

    def test_sgt3(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmBitwiseLogicOperation/sgt3.json
            sha256sum: 38692c44b2cb02fe8f4bc0b6206a9fa86ec431681a26e2c0320a346b14b612ec
            Code: PUSH32 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
                  PUSH1 0x0
                  SGT
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff600013600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000000000,
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff600013600055'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0x01)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 79988)

    def test_lt0(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmBitwiseLogicOperation/lt0.json
            sha256sum: 413acc856062bd46cb06eb78649854dc0d8a831034dee0a1ef072f2cfb37566b
            Code: PUSH1 0x0
                  PUSH1 0x2
                  PUSH1 0x0
                  SUB
                  LT
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('6000600260000310600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=100000000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f3947def4cf144679da39c4c32bdc35681
        value = 10000000000000000000
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
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('6000600260000310600055'))
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 94982)

    def test_gt2(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmBitwiseLogicOperation/gt2.json
            sha256sum: 0cacb5dab6cc89774aa97e6d252c43f9018d0f9a87a2ca3c82a328cb13b9715f
            Code: PUSH1 0x0
                  PUSH32 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
                  GT
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('60007fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff11600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000000000,
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('60007fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff11600055'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0x01)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 79988)

    def test_byte8(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmBitwiseLogicOperation/byte8.json
            sha256sum: abf115e329153cc0530da72c93e8eee7497db8e0bc2a5ea49359a8b7db1fbc6e
            Code: PUSH8 0x8040201008040201
                  PUSH1 0x1f
                  PUSH1 0x1f
                  SUB
                  BYTE
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('678040201008040201601f601f031a600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000000000,
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('678040201008040201601f601f031a600055'))
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 94982)

    def test_byteBN(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmBitwiseLogicOperation/byteBN.json
            sha256sum: 9564cce3b1322985dd78e9be695612b7ce4380d10bff5ff9629e91a890bc9a4a
            Code: PUSH5 0x1234523456
                  PUSH1 0x1f
                  BYTE
                  DUP1
                  ADD
                  PUSH1 0x1
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('641234523456601f1a8001600155')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000000000,
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('641234523456601f1a8001600155'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x01)), 0xac)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 79982)

    def test_and4(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmBitwiseLogicOperation/and4.json
            sha256sum: f87ad97d5172476fc9fd62b351d6e80130da68ef9c11f166db1566c227488654
            Code: PUSH32 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
                  PUSH32 0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee
                  AND
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7feeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee16600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000000000,
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7feeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee16600055'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 79988)

    def test_xor2(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmBitwiseLogicOperation/xor2.json
            sha256sum: 2f0a55f83be0e7d94b623f0f09cc88ef2891842d650eebe48c00987c987330d7
            Code: PUSH1 0x1
                  PUSH1 0x3
                  XOR
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('6001600318600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000000000,
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('6001600318600055'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0x02)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 79988)

    def test_byte10(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmBitwiseLogicOperation/byte10.json
            sha256sum: d4adfe1db3c97d31ab6d4be4ec423e473d1693ba4d9b973e1c53ba617f0901fb
            Code: PUSH8 0x8040201008040201
                  PUSH32 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
                  BYTE
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('6780402010080402017fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff1a600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000000000,
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('6780402010080402017fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff1a600055'))
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 94988)

    def test_sgt1(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmBitwiseLogicOperation/sgt1.json
            sha256sum: 89c0ce8917afdbf98d2f4e5fd2f2815cd2858443431bcdc8d7690f88a736c378
            Code: PUSH1 0x2
                  PUSH1 0x0
                  SUB
                  PUSH1 0x0
                  SGT
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('6002600003600013600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000000000,
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('6002600003600013600055'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0x01)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 79982)

    def test_xor1(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmBitwiseLogicOperation/xor1.json
            sha256sum: 4b2e4434cbffa09075795844cc66de408c38012241a270df57ad2da28eda4d45
            Code: PUSH1 0x1
                  PUSH1 0x2
                  XOR
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('6001600218600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000000000,
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('6001600218600055'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0x03)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 79988)

    def test_or2(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmBitwiseLogicOperation/or2.json
            sha256sum: ab4e1ba965e4c02e768f8bf82e7ed24167a8d56b0779c40f046ce78819aeb5b9
            Code: PUSH1 0x1
                  PUSH1 0x3
                  OR
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('6001600317600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000000000,
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('6001600317600055'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0x03)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 79988)

    def test_byte4(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmBitwiseLogicOperation/byte4.json
            sha256sum: 7a9e609c4022284ea71b3671e523b44c35e561fc12db0a259f32a54aeea0396f
            Code: PUSH8 0x8040201008040201
                  PUSH1 0x4
                  PUSH1 0x1f
                  SUB
                  BYTE
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('6780402010080402016004601f031a600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000000000,
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('6780402010080402016004601f031a600055'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0x10)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 79982)

    def test_lt2(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmBitwiseLogicOperation/lt2.json
            sha256sum: 4c18ec8032b73146c3cc964f2e2b589f688979c2a25be96ea9ff6399d22a252a
            Code: PUSH1 0x0
                  PUSH32 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
                  LT
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('60007fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff10600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=10000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f3947def4cf144679da39c4c32bdc35681
        value = 10000000000000000000
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 10000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('60007fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff10600055'))
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 94988)

    def test_not3(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmBitwiseLogicOperation/not3.json
            sha256sum: 88f4c46fa17db91530782f3cc95d87e7337c4ce0d2c9987ef15746d2c7a5eb38
            Code: PUSH1 0x2
                  PUSH1 0x0
                  SUB
                  NOT
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('600260000319600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000000000,
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('600260000319600055'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0x01)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 79985)

    def test_gt0(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmBitwiseLogicOperation/gt0.json
            sha256sum: 7cb8d628774fa8e190bf009d3e7bece12193623c672664764626af200bec107a
            Code: PUSH1 0x0
                  PUSH1 0x2
                  PUSH1 0x0
                  SUB
                  GT
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('6000600260000311600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000000000,
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('6000600260000311600055'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0x01)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 79982)

    def test_byte2(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmBitwiseLogicOperation/byte2.json
            sha256sum: bdd45957ea15b4979531077f732ef803c1645456cf90115220f4ff615124c8e4
            Code: PUSH8 0x8040201008040201
                  PUSH1 0x2
                  PUSH1 0x1f
                  SUB
                  BYTE
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('6780402010080402016002601f031a600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000000000,
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('6780402010080402016002601f031a600055'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0x04)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 79982)

    def test_and1(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmBitwiseLogicOperation/and1.json
            sha256sum: 22f9a7c527f12ff84d6556ecda94f19444a0733b7457ffb28e6b4018085a0624
            Code: PUSH1 0x1
                  PUSH1 0x2
                  AND
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('6001600216600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000000000,
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('6001600216600055'))
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 94988)

    def test_not1(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmBitwiseLogicOperation/not1.json
            sha256sum: 32acbe473061049f3a2f1e448e6c4d3ec331d3338104789c3b8f350336b35229
            Code: PUSH1 0x2
                  NOT
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('600219600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000000000,
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('600219600055'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffd)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 79991)

    def test_byte6(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmBitwiseLogicOperation/byte6.json
            sha256sum: ed258fd3ddb306ebce41848e25eb84664d797106ec14c74f81134a5df60b36e9
            Code: PUSH8 0x8040201008040201
                  PUSH1 0x6
                  PUSH1 0x1f
                  SUB
                  BYTE
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('6780402010080402016006601f031a600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000000000,
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('6780402010080402016006601f031a600055'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0x40)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 79982)

    def test_byte5(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmBitwiseLogicOperation/byte5.json
            sha256sum: 6f638578a373e8fddb401298e434d59df16a2e1dd58df56a41ce611a9218c93f
            Code: PUSH8 0x8040201008040201
                  PUSH1 0x5
                  PUSH1 0x1f
                  SUB
                  BYTE
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('6780402010080402016005601f031a600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000000000,
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('6780402010080402016005601f031a600055'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0x20)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 79982)

    def test_slt4(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmBitwiseLogicOperation/slt4.json
            sha256sum: df3e08187c7fe98999863d21c754f7a8b21c08cfc69a5e6ec2d43f38478a4bf4
            Code: PUSH1 0x3
                  PUSH1 0x0
                  SUB
                  PUSH1 0x5
                  PUSH1 0x0
                  SUB
                  SLT
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('6003600003600560000312600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000000000,
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('6003600003600560000312600055'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0x01)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 79976)

    def test_iszero1(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmBitwiseLogicOperation/iszero1.json
            sha256sum: 1a077b6b773a8bdce8ebae6fd6739dadb1d52c6ef9cc4a56ccf2e669082effb7
            Code: PUSH1 0x0
                  ISZERO
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('600015600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000000000,
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('600015600055'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0x01)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 79991)

    def test_xor5(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmBitwiseLogicOperation/xor5.json
            sha256sum: 455eb5861cb53aa17ea10552b59d45dca88889395d86cf5145389636fa3e7d11
            Code: PUSH32 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
                  PUSH32 0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeefeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee
                  XOR
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7feeeeeeeeeeeeeeeeeeeeeeeeeeeeefeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee18600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000000000,
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7feeeeeeeeeeeeeeeeeeeeeeeeeeeeefeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee18600055'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0x1111111111111111111111111111101111111111111111111111111111111111)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 79988)

    def test_and5(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmBitwiseLogicOperation/and5.json
            sha256sum: 3729f0f7fc8185b76c1a2bdb17469320551347cf5655a3881bf30aee5bd50bbd
            Code: PUSH32 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
                  PUSH32 0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeefeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee
                  AND
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7feeeeeeeeeeeeeeeeeeeeeeeeeeeeefeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee16600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000000000,
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7feeeeeeeeeeeeeeeeeeeeeeeeeeeeefeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee16600055'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeefeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 79988)

    def test_eq2(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmBitwiseLogicOperation/eq2.json
            sha256sum: b7335c7c95c2a5a46510c70f6de9301743b4afa0961af71ddf47fe9a4fa83fd6
            Code: PUSH32 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
                  PUSH32 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
                  EQ
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff14600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000000000,
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff14600055'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0x01)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 79988)

    def test_byte9(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmBitwiseLogicOperation/byte9.json
            sha256sum: a8d92c39ed4e8d9a1732c79f914c749ac5ddc2f5298106c592490f712acd0781
            Code: PUSH8 0x8040201008040201
                  PUSH1 0x20
                  PUSH1 0x1f
                  SDIV
                  BYTE
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('6780402010080402016020601f051a600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000000000,
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('6780402010080402016020601f051a600055'))
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 94980)

    def test_iszeo2(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmBitwiseLogicOperation/iszeo2.json
            sha256sum: dcb7e61a20a783155b42ff320797c583377e997c8317f1c0a20dbebc0eeddbcf
            Code: PUSH1 0x2
                  PUSH1 0x0
                  SUB
                  ISZERO
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('600260000315600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000000000,
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('600260000315600055'))
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 94985)

    def test_lt1(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmBitwiseLogicOperation/lt1.json
            sha256sum: 579f05f2db2f72c163d6de8b56e16591a3e8de8c7c255a7af9a2a9e916385c30
            Code: PUSH1 0x2
                  PUSH1 0x0
                  SUB
                  PUSH1 0x0
                  LT
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('6002600003600010600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=10000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f3947def4cf144679da39c4c32bdc35681
        value = 10000000000000000000
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 10000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('6002600003600010600055'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0x01)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 79982)

    def test_gt3(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmBitwiseLogicOperation/gt3.json
            sha256sum: fdbea629c2b538e85a2b47cff6723eb757ec9827386fc2447b4ec40582c97547
            Code: PUSH32 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
                  PUSH1 0x0
                  GT
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff600011600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000000000,
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff600011600055'))
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 94988)

    def test_not2(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmBitwiseLogicOperation/not2.json
            sha256sum: 475440cd5563de1d27adaac0eb4be286874f2448b61465406397751d71a9b476
            Code: PUSH32 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
                  NOT
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff19600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000000000,
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff19600055'))
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 94991)

    def test_slt2(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmBitwiseLogicOperation/slt2.json
            sha256sum: a6e5a6dfe8f2cc55bce8abcbbe6b6f02aa8af89fb220fad1fd7d6188965c3a64
            Code: PUSH1 0x0
                  PUSH32 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
                  SLT
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('60007fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff12600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000000000,
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('60007fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff12600055'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0x01)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 79988)

    def test_xor4(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmBitwiseLogicOperation/xor4.json
            sha256sum: c7319a9ed20207d1d16402b8f0c5e314b0c9437d483f8edad93c77e0dd3158bb
            Code: PUSH32 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
                  PUSH32 0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee
                  XOR
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7feeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee18600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000000000,
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7feeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee18600055'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0x1111111111111111111111111111111111111111111111111111111111111111)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 79988)

if __name__ == '__main__':
    unittest.main()
