
#Taken from /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest
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

evm.DEFAULT_FORK = "frontier"
class EVMTest_vmArithmeticTest(unittest.TestCase):
    _multiprocess_can_split_ = True
    maxDiff=None 


    def test_addmodDivByZero1(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: addmodDivByZero1.json
            sha256sum: cb6142b733dd0a41e5e83b98921b62dbed0c90e28da43109e7189cc37e20bc9d
            Code: PUSH1 0x0
                  PUSH1 0x1
                  PUSH1 0x0
                  ADDMOD
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('60006001600008600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('60006001600008600055'))
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 94980)

    def test_mulmod2_0(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: mulmod2_0.json
            sha256sum: cc684081a03672440715b213e55d41c6b40b5f906d5729227eca121ffb459d9f
            Code: PUSH1 0x3
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
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('60036001600560000309600360056000030714600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('60036001600560000309600360056000030714600055'))
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 94954)

    def test_expPowerOf2_64(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: expPowerOf2_64.json
            sha256sum: 0a917c261c69f13064e5ca6c65b8f3fa61ee9013526b33ae828887b0605b8d0f
            Code: PUSH1 0x40
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
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('604060020a600055603f60020a600155604160020a600255')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('604060020a600055603f60020a600155604160020a600255'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0x010000000000000000)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x01)), 0x8000000000000000)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x02)), 0x020000000000000000)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 39913)

    def test_sdiv5(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: sdiv5.json
            sha256sum: 024224e1f6e953cab5d5c8c00eb01e65eaba45104cce696fa37b6f1304676e6c
            Code: PUSH1 0x1
                  PUSH1 0x0
                  SUB
                  PUSH32 0x8000000000000000000000000000000000000000000000000000000000000000
                  PUSH1 0x0
                  SUB
                  SDIV
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('60016000037f800000000000000000000000000000000000000000000000000000000000000060000305600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('60016000037f800000000000000000000000000000000000000000000000000000000000000060000305600055'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0x8000000000000000000000000000000000000000000000000000000000000000)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 79974)

    def test_expPowerOf256Of256_0(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: expPowerOf256Of256_0.json
            sha256sum: 90140ff94b6bfacb841fe9ec94969da8c2ff50d4a298e567ab9e2bc3924684cd
            Code: PUSH1 0x0
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
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=10000000)
    
        bytecode = unhexlify('60006101000a6101000a600055600060ff0a6101000a60015560006101010a6101000a60025560006101000a60ff0a600355600060ff0a60ff0a60045560006101010a60ff0a60055560006101000a6101010a600655600060ff0a6101010a60075560006101010a6101010a600855')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 1000000

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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('60006101000a6101000a600055600060ff0a6101000a60015560006101010a6101000a60025560006101000a60ff0a600355600060ff0a60ff0a60045560006101010a60ff0a60055560006101000a6101010a600655600060ff0a6101010a60075560006101010a6101010a600855'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0x0100)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x01)), 0x0100)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x02)), 0x0100)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x03)), 0xff)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x04)), 0xff)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x05)), 0xff)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x06)), 0x0101)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x07)), 0x0101)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x08)), 0x0101)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 819622)

    def test_sdiv0(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: sdiv0.json
            sha256sum: f247d5d6906019548216c29459efebace369512d19df0e266ecc8a2028dc1960
            Code: PUSH32 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
                  PUSH32 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
                  PUSH1 0x0
                  SUB
                  SDIV
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff60000305600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff60000305600055'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 79980)

    def test_expPowerOf2_256(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: expPowerOf2_256.json
            sha256sum: 5b5b5e2fdf3149601d208e55b5a19c527a74f554b7024514a5a14c10a827021b
            Code: PUSH2 0x100
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
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('61010060020a60005560ff60020a60015561010160020a600255')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('61010060020a60005560ff60020a60015561010160020a600255'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x01)), 0x8000000000000000000000000000000000000000000000000000000000000000)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 69893)

    def test_expPowerOf256_12(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: expPowerOf256_12.json
            sha256sum: 6961b8ed41be6fab3df3b7ad24004c9513c69ecd51a80f3a54d8f3f0c3598de2
            Code: PUSH1 0xc
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
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('600c6101000a600055600c60ff0a600155600c6101010a600255')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('600c6101000a600055600c60ff0a600155600c6101010a600255'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0x01000000000000000000000000)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x01)), 0xf44125ebeb98e9ee2441f401)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x02)), 0x010c42ddf21b9f19efdc420c01)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 39913)

    def test_expPowerOf256_9(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: expPowerOf256_9.json
            sha256sum: d86d61b53ef010f8122ef525d1d4662b9b6a680256aebca4630918e07de611f0
            Code: PUSH1 0x9
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
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('60096101000a600055600960ff0a60015560096101010a600255')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('60096101000a600055600960ff0a60015560096101010a600255'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0x01000000000000000000)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x01)), 0xf723ac7d8253dc08ff)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x02)), 0x010924547e7e54240901)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 39913)

    def test_expPowerOf2_8(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: expPowerOf2_8.json
            sha256sum: dc827c7432f16db5c78b63f434ca2dc24762a4bf7827cc3f487fffe08a0d452c
            Code: PUSH1 0x8
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
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('600860020a600055600760020a600155600960020a600255')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('600860020a600055600760020a600155600960020a600255'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0x0100)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x01)), 0x80)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x02)), 0x0200)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 39913)

    def test_expPowerOf256_28(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: expPowerOf256_28.json
            sha256sum: 1a20d105592e063cd1a2736383aba235513940ea6a3e91fea29aa0db06e1f88f
            Code: PUSH1 0x1c
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
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('601c6101000a600055601c60ff0a600155601c6101010a600255')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('601c6101000a600055601c60ff0a600155601c6101010a600255'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0x0100000000000000000000000000000000000000000000000000000000)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x01)), 0xe56d8280c5c1dc6be448760a77f47c1750f146fd962467ee3579e401)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x02)), 0x011d871d80b9e4ff369ba3f4b3ce9beb6f2bb9931fe9243807cd7a1c01)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 39913)

    def test_expPowerOf256Of256_32(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: expPowerOf256Of256_32.json
            sha256sum: 3aeec0dc1d899e00954d8cc12a7eb4e4ea8a79d53b763de0ed38bbd7f70dc8e0
            Code: PUSH1 0x20
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
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=10000000)
    
        bytecode = unhexlify('60206101000a6101000a600055602060ff0a6101000a60015560206101010a6101000a60025560206101000a60ff0a600355602060ff0a60ff0a60045560206101010a60ff0a60055560206101000a6101010a600655602060ff0a6101010a60075560206101010a6101010a600855')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 1000000

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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('60206101000a6101000a600055602060ff0a6101000a60015560206101010a6101000a60025560206101000a60ff0a600355602060ff0a60ff0a60045560206101010a60ff0a60055560206101000a6101010a600655602060ff0a6101010a60075560206101010a6101010a600855'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0x01)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x03)), 0x01)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x04)), 0xb8247842bb5ce75c08d0c251669ed5870fa24a22952e5db3a7c66c59ffe000ff)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x05)), 0xee526e5a06f2a990b2bf6c951e5feabf0e07ee16877296e1be872db9e02000ff)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x06)), 0x01)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x07)), 0xeda7d024b6de40a9d3b966e71f10a4667edc5b71cab07aeabcac6249dfe00101)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x08)), 0x512ecfaeeb11205f0833e1054dcb1300488e0954be5af77a49e143aa00200101)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 847702)

    def test_expPowerOf256_13(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: expPowerOf256_13.json
            sha256sum: 7175a5c1d4422f0a80afaf7e92eff51584e1529057d43a7cc177cc4cc6ddb491
            Code: PUSH1 0xd
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
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('600d6101000a600055600d60ff0a600155600d6101010a600255')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('600d6101000a600055600d60ff0a600155600d6101010a600255'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0x0100000000000000000000000000)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x01)), 0xf34ce4c5ffad5104361db20cff)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x02)), 0x010d4f20d00dbab909cc1e4e0d01)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 39913)

    def test_expPowerOf256_20(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: expPowerOf256_20.json
            sha256sum: b0740a6ca31abb6604729d5c5904c1c79842624834b8c01a0b3dfec6c470313e
            Code: PUSH1 0x14
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
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('60146101000a600055601460ff0a60015560146101010a600255')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('60146101000a600055601460ff0a60015560146101010a600255'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0x010000000000000000000000000000000000000000)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x01)), 0xecb99eb1063b1984b725d2e3c72b82e88cbdec01)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x02)), 0x0114c2872a2898bea4ec46054167a4a2f174be1401)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 39913)

    def test_divByZero(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: divByZero.json
            sha256sum: 3c90b75a836a6d2f79054eb6bb179afa94045229bbf98f4f0ef6603d353cc7bd
            Code: PUSH1 0x0
                  PUSH1 0x2
                  DIV
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('6000600204600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('6000600204600055'))
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 94986)

    def test_expPowerOf256Of256_33(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: expPowerOf256Of256_33.json
            sha256sum: 8f763116e64155dbe53aaf5f769a7daf990afb49965141af4cc8ca4fa9b9e4e4
            Code: PUSH1 0x21
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
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=10000000)
    
        bytecode = unhexlify('60216101000a6101000a600055602160ff0a6101000a60015560216101010a6101000a60025560216101000a60ff0a600355602160ff0a60ff0a60045560216101010a60ff0a60055560216101000a6101010a600655602160ff0a6101010a60075560216101010a6101010a600855')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 1000000

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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('60216101000a6101000a600055602160ff0a6101000a60015560216101010a6101000a60025560216101000a60ff0a600355602160ff0a60ff0a60045560216101010a60ff0a60055560216101000a6101010a600655602160ff0a6101010a60075560216101010a6101010a600855'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0x01)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x03)), 0x01)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x04)), 0x8dcb65b5494eba78cd6756a6f9851f6e26d0f2bb9ecd7e9abd7e9b11209ffeff)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x05)), 0x6694bb31b20cd625f3756897dae6d738f2e64467b5b6f10fa3e07763ffa100ff)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x06)), 0x01)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x07)), 0xe678999aeffd1f1f45081f64de7f80ab083dd7df04721ed64ee04c03bda1ff01)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x08)), 0x39b68fb9898dd7568abd178397251ce8226a25c1d305a4e79573333520a10101)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 847702)

    def test_expPowerOf256_22(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: expPowerOf256_22.json
            sha256sum: 13cfb8aaf7225968816d16a4431dec7b1450c365dd74bb1d5e77964ce04d8907
            Code: PUSH1 0x16
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
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('60166101000a600055601660ff0a60015560166101010a600255')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('60166101000a600055601660ff0a60015560166101010a600255'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0x0100000000000000000000000000000000000000000000)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x01)), 0xeae1182d42dfa98cc73c3e63d280f30e3e8cfce6ea01)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x02)), 0x0116ed20fb041418baf4c37d91efb553dbfa9904e71601)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 39913)

    def test_signextend_BigByte_0(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: signextend_BigByte_0.json
            sha256sum: 55f9f4e253517d1ac56053c4e71c32eb1b18d40d5ea754683851ea356ae9daa1
            Code: PUSH1 0x0
                  PUSH32 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
                  SIGNEXTEND
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=10000000)
    
        bytecode = unhexlify('60007fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0b600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 1000000

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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('60007fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0b600055'))
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 994986)

    def test_mul1(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: mul1.json
            sha256sum: c27023f53c812b9cbb868e7f76fc946c62869666668f44cf8fa85660c373d01d
            Code: PUSH32 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
                  PUSH32 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
                  MUL
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff02600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff02600055'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0x01)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 79986)

    def test_exp7(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: exp7.json
            sha256sum: fc5158a5d8f866285b0dc0feab44a7f04cd9d5c70392ac3a121ee7f5f449b92b
            Code: PUSH2 0x101
                  PUSH1 0x2
                  EXP
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('61010160020a600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('61010160020a600055'))
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 94961)

    def test_expPowerOf256Of256_29(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: expPowerOf256Of256_29.json
            sha256sum: 7e5cd980778372fddd4fe5da72d58a03f7248ea522d4ff1cee8774289648dd19
            Code: PUSH1 0x1d
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
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=10000000)
    
        bytecode = unhexlify('601d6101000a6101000a600055601d60ff0a6101000a600155601d6101010a6101000a600255601d6101000a60ff0a600355601d60ff0a60ff0a600455601d6101010a60ff0a600555601d6101000a6101010a600655601d60ff0a6101010a600755601d6101010a6101010a600855')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 1000000

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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('601d6101000a6101000a600055601d60ff0a6101000a600155601d6101010a6101000a600255601d6101000a60ff0a600355601d60ff0a60ff0a600455601d6101010a60ff0a600555601d6101000a6101010a600655601d60ff0a6101010a600755601d6101010a6101010a600855'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x03)), 0xff7f000000000000000000000000000000000000000000000000000000000001)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x04)), 0x41e065d46e0349cfe624c4e8a2034aea1f7edfff80e511cd8067d488949bfeff)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x05)), 0xa84162ca6675a22c4c79dfc4ea15f760db5a04dbf04246764199b668879d00ff)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x06)), 0xff81000000000000000000000000000000000000000000000000000000000001)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x07)), 0x1226984faa6b05ebdbd45d8477fa4fd5b55bfd5061de03c319282b153d9dff01)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x08)), 0x5cc9e6b0b749fd94541ad00364bdec2fca7816981ca3e38f485decc7a49d0101)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 861952)

    def test_expPowerOf256_33(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: expPowerOf256_33.json
            sha256sum: f2daf3916252f2d92a191ca8ec40e6a6394d64b697e9b1efe88e75200d711db7
            Code: PUSH1 0x21
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
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('60216101000a600055602160ff0a60015560216101010a600255')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('60216101000a600055602160ff0a60015560216101010a600255'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x01)), 0xfb4c498e11e3f82e714be514ef024675bb48d678bd192222cd2e783d4df020ff)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x02)), 0x25f3884075dd08b8fb400789097aa95df8750bd17be0d83c9a0fb7ed52102101)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 54913)

    def test_addmod3(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: addmod3.json
            sha256sum: e5b07da689ffac562e99efc151d2c9e85f8ec9d86b0a232c66722f0ed279ef47
            Code: PUSH1 0x3
                  PUSH1 0x0
                  SUB
                  PUSH1 0x1
                  PUSH1 0x4
                  ADDMOD
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('60036000036001600408600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('60036000036001600408600055'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0x05)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 79974)

    def test_sdivByZero0(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: sdivByZero0.json
            sha256sum: d6e23171cfe8625fb39ce7d15d8b72776b0c2854017aadeff0bc2458983a76d1
            Code: PUSH1 0x0
                  PUSH1 0x0
                  SUB
                  PUSH1 0x3
                  PUSH1 0x0
                  SUB
                  SDIV
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('6000600003600360000305600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('6000600003600360000305600055'))
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 94974)

    def test_mod4(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: mod4.json
            sha256sum: e331db234769811883d87ea184e6e1ac118b59906328047791f12e2461435a20
            Code: PUSH1 0x3
                  PUSH1 0x2
                  PUSH1 0x0
                  SUB
                  MOD
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('6003600260000306600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('6003600260000306600055'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0x02)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 79980)

    def test_expPowerOf256Of256_6(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: expPowerOf256Of256_6.json
            sha256sum: a5e79941b4ad22e16675c01093e4641e21c12e304fb056cd48e99cd32659982e
            Code: PUSH1 0x6
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
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=10000000)
    
        bytecode = unhexlify('60066101000a6101000a600055600660ff0a6101000a60015560066101010a6101000a60025560066101000a60ff0a600355600660ff0a60ff0a60045560066101010a60ff0a60055560066101000a6101010a600655600660ff0a6101010a60075560066101010a6101010a600855')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 1000000

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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('60066101000a6101000a600055600660ff0a6101000a60015560066101010a6101000a60025560066101000a60ff0a600355600660ff0a60ff0a60045560066101010a60ff0a60055560066101000a6101010a600655600660ff0a6101010a60075560066101010a6101010a600855'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x03)), 0x1948059de1def03c4ec35fc22c2bb8f2bf45dc33085514ff7f00000000000001)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x04)), 0x41f818a8e24eb6d7bb7b193b4f2b5fdcf4bd0d453f2ac3499d8830d391fa00ff)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x05)), 0xede6fe4a943dfb5d967a2b85d6728759d40d2ef0ae4bc28bbb1867f98c0600ff)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x06)), 0x083c936cbaad5de592badc2e142fe4ebd6103921f7aa6aff8100000000000001)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x07)), 0x57385019fe4e0939ca3f35c37cadfaf52fba5b1cdfb02def3866e8068bfa0101)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x08)), 0x810ac878bd98428f6be8c6426ba9f9da09e3e33bf4fe10bfa3f8b12c92060101)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 864022)

    def test_expXY(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: expXY.json
            sha256sum: 946461d4eabea507c8507010fd972cc8a0bc845d05865cf9eabbb5e93b7a169a
            Code: PUSH1 0x0
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
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('6000356000556020356001556001546000540a600255')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = unhexlify('0000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000100000000000f')
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('6000356000556020356001556001546000540a600255'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0x02)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x01)), 0x0100000000000f)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 54793)

    def test_mulmod2_1(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: mulmod2_1.json
            sha256sum: 0c688ca9972d5d25c4dfe4fbc99c6b6796773acbdf9076afa799682c3e60ca7e
            Code: PUSH1 0x3
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
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('60036001600560000309600360056000030614600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('60036001600560000309600360056000030614600055'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0x01)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 79954)

    def test_expPowerOf256Of256_3(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: expPowerOf256Of256_3.json
            sha256sum: ed99ceec8519b10c02299fa905e9822071e3457d195206d67a29dca715949fd5
            Code: PUSH1 0x3
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
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=10000000)
    
        bytecode = unhexlify('60036101000a6101000a600055600360ff0a6101000a60015560036101010a6101000a60025560036101000a60ff0a600355600360ff0a60ff0a60045560036101010a60ff0a60055560036101000a6101010a600655600360ff0a6101010a60075560036101010a6101010a600855')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 1000000

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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('60036101000a6101000a600055600360ff0a6101000a60015560036101010a6101000a60025560036101000a60ff0a600355600360ff0a60ff0a60045560036101010a60ff0a60055560036101000a6101010a600655600360ff0a6101010a60075560036101010a6101010a600855'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x03)), 0x109a00e1370d2d2922bf892e85becb54297354b2e5c75388d514ff7f00000001)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x04)), 0x54a792f15e9aba7e4ad9e716bc169eea3a6e2e9c49bf9b335874613c8081feff)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x05)), 0x5d24a14d8e5e039372cd0f6a0f31e9ed6b75adba9f16b1c5b3edd5ba818300ff)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x06)), 0x298e2f316b4ccded5ebf515998d9ec20df69404b04a441782a6aff8100000001)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x07)), 0x4335694e98f372183c62a2339fa4ad161e9b4c42240bdc9452abffd07783ff01)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x08)), 0xf0f0820797315acd063056bba76f6a9c3e281cdb5197a233967ca94684830101)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 864292)

    def test_expPowerOf256Of256_10(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: expPowerOf256Of256_10.json
            sha256sum: 0248bad71261f2ebe6476f4ed0ca91e98062b440c738386dde95fc76da51e826
            Code: PUSH1 0xa
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
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=10000000)
    
        bytecode = unhexlify('600a6101000a6101000a600055600a60ff0a6101000a600155600a6101010a6101000a600255600a6101000a60ff0a600355600a60ff0a60ff0a600455600a6101010a60ff0a600555600a6101000a6101010a600655600a60ff0a6101010a600755600a6101010a6101010a600855')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 1000000

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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('600a6101000a6101000a600055600a60ff0a6101000a600155600a6101010a6101000a600255600a6101000a60ff0a600355600a60ff0a60ff0a600455600a6101010a60ff0a600555600a6101000a6101010a600655600a60ff0a6101010a600755600a6101010a6101010a600855'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x03)), 0xfe0f60957dc223578a0298879ec55c33085514ff7f0000000000000000000001)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x04)), 0xc1ea45f348b5d351c4d8fe5c77da979cadc33d866acc42e981278896b1f600ff)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x05)), 0x56ddb29bca94fb986ac0a40188b3b53f3216b3559bd8324a77ea8bd8a80a00ff)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x06)), 0x2d49ff6b0bbe177ae9317000b68fb921f7aa6aff810000000000000000000001)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x07)), 0x185fa9eab94cfe3016b69657e83b23fd24cc6960218254231c3db627a7f60101)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x08)), 0xa7a0223829f26d6c635368034320563df4aa5eb62efc87a42bb35f69b20a0101)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 863662)

    def test_expPowerOf256Of256_17(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: expPowerOf256Of256_17.json
            sha256sum: efdafd61b4d2430c56294205b0389c494d8d35733419d89e2189884ec84ffb0e
            Code: PUSH1 0x11
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
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=10000000)
    
        bytecode = unhexlify('60116101000a6101000a600055601160ff0a6101000a60015560116101010a6101000a60025560116101000a60ff0a600355601160ff0a60ff0a60045560116101010a60ff0a60055560116101000a6101010a600655601160ff0a6101010a60075560116101010a6101010a600855')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 1000000

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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('60116101000a6101000a600055601160ff0a6101000a60015560116101010a6101000a60025560116101000a60ff0a600355601160ff0a60ff0a60045560116101010a60ff0a60055560116101000a6101010a600655601160ff0a6101010a60075560116101010a6101010a600855'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x03)), 0xec698218879ec55c33085514ff7f000000000000000000000000000000000001)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x04)), 0x722ad218eb1995a2d257c4c06d8de993c203cfc8e3512df7d633e17e908ffeff)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x05)), 0x8ac9b5ec08d74612cb29f941481d274b51721af2296207c0da8d24667f9100ff)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x06)), 0x8fc9b0f000b68fb921f7aa6aff81000000000000000000000000000000000001)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x07)), 0x81d5ff63680841482299f3eab616446dcd336f537c0c565aa4112ab95d91ff01)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x08)), 0x9c6ca90dac4e97dea02ac969e8649ee9e6232e0c3f4797411151cb8f90910101)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 863032)

    def test_expPowerOf256Of256_27(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: expPowerOf256Of256_27.json
            sha256sum: a1d19ca0171c8b91922a91db49e2f3faadd95be335783b97f016247f240224c0
            Code: PUSH1 0x1b
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
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=10000000)
    
        bytecode = unhexlify('601b6101000a6101000a600055601b60ff0a6101000a600155601b6101010a6101000a600255601b6101000a60ff0a600355601b60ff0a60ff0a600455601b6101010a60ff0a600555601b6101000a6101010a600655601b60ff0a6101010a600755601b6101010a6101010a600855')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 1000000

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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('601b6101000a6101000a600055601b60ff0a6101000a600155601b6101010a6101000a600255601b6101000a60ff0a600355601b60ff0a60ff0a600455601b6101010a60ff0a600555601b6101000a6101010a600655601b60ff0a6101010a600755601b6101010a6101010a600855'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x03)), 0x5514ff7f00000000000000000000000000000000000000000000000000000001)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x04)), 0x178918ffbcb401d4efd2f7dfb4d01a897172267f0f491121ac52dd614899feff)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x05)), 0x38ecff71480ca0b422f2ed6f780d5fead2ae234a49104b10a86f7f0dd19b00ff)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x06)), 0xaa6aff8100000000000000000000000000000000000000000000000000000001)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x07)), 0xd02811cb5dc1d80567e810532b235b7672f5c78cd6e89bb511d5e2d8f79bff01)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x08)), 0x1b4e6404f474c18055d30bb8987672f59e97980d6f9de1764c0fbec5ec9b0101)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 862132)

    def test_expPowerOf256_21(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: expPowerOf256_21.json
            sha256sum: abd10e17d688e09619790af67c0553c0fafb05374496c5dcac20c86635771fd3
            Code: PUSH1 0x15
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
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('60156101000a600055601560ff0a60015560156101010a600255')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('60156101000a600055601560ff0a60015560156101010a600255'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0x01000000000000000000000000000000000000000000)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x01)), 0xebcce5125534de6b326ead10e3645765a4312e14ff)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x02)), 0x0115d749b152c1576391324b46a90c47946632d21501)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 39913)

    def test_addmodDivByZero3(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: addmodDivByZero3.json
            sha256sum: c66eaa3ef9cc720a3194d2e4031d7f285eabb2f529931057fcaa06efbf4b8453
            Code: PUSH1 0x1
                  PUSH1 0x0
                  PUSH1 0x0
                  PUSH1 0x0
                  ADDMOD
                  SUB
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('60016000600060000803600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('60016000600060000803600055'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 79974)

    def test_expPowerOf256_16(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: expPowerOf256_16.json
            sha256sum: b3912160e11fd495497ba6bc62cc649cf5572048412234be7b2a023d298a14c7
            Code: PUSH1 0x10
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
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('60106101000a600055601060ff0a60015560106101010a600255')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('60106101000a600055601060ff0a60015560106101010a600255'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0x0100000000000000000000000000000000)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x01)), 0xf075d70b0f1b82196f36f719d077f001)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x02)), 0x01107a372d2f74e272cf59171e30781001)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 39913)

    def test_exp1(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: exp1.json
            sha256sum: 2d558bca9c3748e933bf10ae3ed17cb8a9ffbaf12afbe5d03e56ec266ea7842c
            Code: PUSH32 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe
                  PUSH32 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
                  EXP
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0a600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0a600055'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0x01)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 79661)

    def test_sdiv_dejavu(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: sdiv_dejavu.json
            sha256sum: 452081e3e414078883f6a88fe922841ab480e6786afd74e40ff8cb960db4cb9d
            Code: PUSH1 0x5
                  PUSH1 0x9
                  PUSH1 0x0
                  SUB
                  SDIV
                  DUP1
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('600560096000030580600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x1
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 10000000

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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('600560096000030580600055'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 9979977)

    def test_addmodBigIntCast(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: addmodBigIntCast.json
            sha256sum: 241ccaee5295d1b7015b0c489f5463d7be34619033e089550a114e191782242b
            Code: PUSH1 0x5
                  PUSH1 0x1
                  PUSH32 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
                  ADDMOD
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('600560017fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff08600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('600560017fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff08600055'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0x01)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 79980)

    def test_smod1(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: smod1.json
            sha256sum: 28ae643524b0b1604bf6855fdba96c6a2edee6933e3d4e299296ff1861bce9b6
            Code: PUSH1 0x3
                  PUSH1 0x0
                  SUB
                  PUSH1 0x5
                  SMOD
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('6003600003600507600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('6003600003600507600055'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0x02)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 79980)

    def test_addmod1_overflowDiff(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: addmod1_overflowDiff.json
            sha256sum: 8609abdac8c8de1a6b70f84ffbc4be546844b9c77c6a9e9fa35fd7f987e3fb4c
            Code: PUSH1 0x5
                  PUSH1 0x2
                  PUSH1 0x0
                  SUB
                  PUSH1 0x1
                  PUSH1 0x0
                  SUB
                  ADDMOD
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('60056002600003600160000308600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 1000000

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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('60056002600003600160000308600055'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0x04)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 979968)

    def test_exp2(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: exp2.json
            sha256sum: 7f8a88cc52c669687508ef474246c30a969cdecf4eb6a508600be3dc404317dd
            Code: PUSH4 0x7fffffff
                  PUSH4 0x7fffffff
                  EXP
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('637fffffff637fffffff0a600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('637fffffff637fffffff0a600055'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0xbc8cccccccc888888880000000aaaaaab00000000fffffffffffffff7fffffff)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 79941)

    def test_exp0(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: exp0.json
            sha256sum: 208b278b3eb8274133ca427c82a0ff718fdcfe1871b1b4c0fb9fa3c573b260f4
            Code: PUSH1 0x2
                  PUSH1 0x2
                  EXP
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('600260020a600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('600260020a600055'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0x04)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 79971)

    def test_divByNonZero1(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: divByNonZero1.json
            sha256sum: e9aae6886ceb4107c9b254a1764a4560c32ab4097cbb4b8ebd6aa8dddf20e3de
            Code: PUSH1 0x18
                  PUSH1 0x17
                  DIV
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('6018601704600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('6018601704600055'))
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 94986)

    def test_mod0(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: mod0.json
            sha256sum: c637f138f8fbd9296d552b44d2b5a2fcd30586689eb2310765ca0fb78ee0ebf4
            Code: PUSH1 0x3
                  PUSH1 0x2
                  MOD
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('6003600206600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('6003600206600055'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0x02)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 79986)

    def test_expPowerOf256_8(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: expPowerOf256_8.json
            sha256sum: 9f8782ad28deabc9d357679318ddc65c1fd930005800b8431dc204ebd574e98b
            Code: PUSH1 0x8
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
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('60086101000a600055600860ff0a60015560086101010a600255')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('60086101000a600055600860ff0a60015560086101010a600255'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0x010000000000000000)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x01)), 0xf81bc845c81bf801)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x02)), 0x01081c3846381c0801)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 39913)

    def test_addmod0(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: addmod0.json
            sha256sum: 515208833995d0cf1a7bc89bfef6fb4fd04a059bbdb4187cadc423b99bff0c71
            Code: PUSH1 0x2
                  PUSH1 0x2
                  PUSH1 0x1
                  ADDMOD
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('60026002600108600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('60026002600108600055'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0x01)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 79980)

    def test_expPowerOf256_23(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: expPowerOf256_23.json
            sha256sum: 8320b29b9626226680d60fc6f959fcea0fafe174a5cfd5e9725745291797af15
            Code: PUSH1 0x17
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
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('60176101000a600055601760ff0a60015560176101010a600255')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('60176101000a600055601760ff0a60015560176101010a600255'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0x010000000000000000000000000000000000000000000000)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x01)), 0xe9f63715159cc9e33a7502256eae721b304e6fea0316ff)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x02)), 0x0118040e1bff182cd3afb8410f81a5092fd6939debfd1701)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 39913)

    def test_exp5(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: exp5.json
            sha256sum: ad4694559220ec79dde1ec9c646d8629e4ad97510b81eb2173a727ce3f1d6c1e
            Code: PUSH1 0x1
                  PUSH2 0x101
                  EXP
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('60016101010a600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('60016101010a600055'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0x0101)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 79971)

    def test_expPowerOf256_18(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: expPowerOf256_18.json
            sha256sum: aa7f8d1062b77e9369aac793e914383284edf1024510633984f90254ce34ede5
            Code: PUSH1 0x12
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
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('60126101000a600055601260ff0a60015560126101010a600255')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('60126101000a600055601260ff0a60015560126101010a600255'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0x01000000000000000000000000000000000000)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x01)), 0xee95dbd2d0085a30be71f86293f0d098ee01)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x02)), 0x01129c3c15c100fbac976a98a583f730991201)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 39913)

    def test_expPowerOf256_17(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: expPowerOf256_17.json
            sha256sum: 2a3ef1239a77968bac4ef2b4def123cb9d5390fdbecd1b2924c7a77fbb47cba1
            Code: PUSH1 0x11
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
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('60116101000a600055601160ff0a60015560116101010a600255')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('60116101000a600055601160ff0a60015560116101010a600255'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0x010000000000000000000000000000000000)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x01)), 0xef856134040c669755c7c022b6a77810ff)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x02)), 0x01118ab1645ca45755422870354ea8881101)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 39913)

    def test_smod8_byZero(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: smod8_byZero.json
            sha256sum: bcee748f666d726f3cd0b0d6a76b8c9029e4719aba2a34e8bd59bf1b4c235a49
            Code: PUSH1 0xd
                  PUSH1 0x0
                  PUSH1 0xc8
                  PUSH1 0x0
                  SUB
                  SMOD
                  SUB
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('600d600060c86000030703600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('600d600060c86000030703600055'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff3)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 79974)

    def test_add1(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: add1.json
            sha256sum: fab06ebfaeb71e4017dec55cd4b45472b843d9cb9001b54eb4cfceabeb5141c2
            Code: PUSH1 0x4
                  PUSH32 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
                  ADD
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('60047fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff01600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('60047fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff01600055'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0x03)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 79988)

    def test_expPowerOf256Of256_22(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: expPowerOf256Of256_22.json
            sha256sum: 66b554633cb22c3619a5b10ea3e4a509c37a667e4d83656c59aaf25dd2f36871
            Code: PUSH1 0x16
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
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=10000000)
    
        bytecode = unhexlify('60166101000a6101000a600055601660ff0a6101000a60015560166101010a6101000a60025560166101000a60ff0a600355601660ff0a60ff0a60045560166101010a60ff0a60055560166101000a6101010a600655601660ff0a6101010a60075560166101010a6101010a600855')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 1000000

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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('60166101000a6101000a600055601660ff0a6101000a60015560166101010a6101000a60025560166101000a60ff0a600355601660ff0a60ff0a60045560166101010a60ff0a60055560166101000a6101010a600655601660ff0a6101010a60075560166101010a6101010a600855'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x03)), 0x9ec55c33085514ff7f0000000000000000000000000000000000000000000001)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x04)), 0xec447e662ac08957d7e290a421dbf54c0aaf43aadc9cc465ad0b02f071ea00ff)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x05)), 0xdc9178d3bab470096f01477c859b5f4173986640b659426412a653465c1600ff)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x06)), 0xb68fb921f7aa6aff810000000000000000000000000000000000000000000001)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x07)), 0xdcf0a770777610503596ae0311af46c171151ed45107d7e7bb8f74bb5bea0101)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x08)), 0x4d65773387993928c95c861274232d3fb6f6b7fe1b22e4e61a30e71172160101)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 862582)

    def test_modByZero(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: modByZero.json
            sha256sum: 975e8402d3cdcd650cbe38ddde963ee0f001c44eb91be662ab5ad30d092bf3ec
            Code: PUSH1 0x1
                  PUSH1 0x0
                  PUSH1 0x3
                  MOD
                  SUB
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('6001600060030603600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('6001600060030603600055'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 79980)

    def test_mod3(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: mod3.json
            sha256sum: 3ff47f92fc773259070c4ecd80ecc707390c4bf33c53bf8ede1405e598e4e563
            Code: PUSH1 0x0
                  PUSH1 0x3
                  MOD
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('6000600306600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('6000600306600055'))
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 94986)

    def test_exp8(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: exp8.json
            sha256sum: 69addad625a0054a7142bc765d5242bb82e834f81a9f4eff97398a1594472990
            Code: PUSH1 0x0
                  PUSH1 0x0
                  EXP
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('600060000a600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('600060000a600055'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0x01)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 79981)

    def test_mulmod0(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: mulmod0.json
            sha256sum: 82bfcdf4dcf1fdeb40788305eee151381ec460d0213106206899051184c39283
            Code: PUSH1 0x2
                  PUSH1 0x2
                  PUSH1 0x1
                  MULMOD
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('60026002600109600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('60026002600109600055'))
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 94980)

    def test_expPowerOf256_27(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: expPowerOf256_27.json
            sha256sum: f1fa279d11f40fe6dde87ae675344583f0fad34b69ff60a946544969e6af9c7f
            Code: PUSH1 0x1b
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
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('601b6101000a600055601b60ff0a600155601b6101010a600255')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('601b6101000a600055601b60ff0a600155601b6101010a600255'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0x01000000000000000000000000000000000000000000000000000000)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x01)), 0xe653d6571cdebb270b53c9d44c40bcd425165d5af1157d6ba11aff)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x02)), 0x011c6ab2cdebf906306b38bbf7d6c52648e2d6bc63859e996e5f1b01)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 39913)

    def test_mulmoddivByZero3(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: mulmoddivByZero3.json
            sha256sum: eca0b9c5545b22116e69cf05c171e68e0f1a6ceefd1e6b24b8b06e08a40bea31
            Code: PUSH1 0x0
                  PUSH1 0x0
                  PUSH1 0x0
                  MULMOD
                  PUSH1 0x1
                  SUB
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('60006000600009600103600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('60006000600009600103600055'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0x01)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 79974)

    def test_smod3(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: smod3.json
            sha256sum: b8dd5232d3daa08785f18e4265162f131a9ff7e1d052d5530aa0f7f7d1a9d212
            Code: PUSH32 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
                  PUSH1 0x2
                  PUSH1 0x0
                  SUB
                  SMOD
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff600260000307600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff600260000307600055'))
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 94980)

    def test_mul3(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: mul3.json
            sha256sum: 9af8c2dcaaf217f7d2cbeaf72d910ae893924a3dbc4951b85404a5f050a90784
            Code: PUSH1 0x1
                  PUSH1 0x17
                  MUL
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('6001601702600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('6001601702600055'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0x17)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 79986)

    def test_expPowerOf256_31(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: expPowerOf256_31.json
            sha256sum: 03ddf07eca732084776985584806b3a2b90af3536705f92c286daa0f723f46c3
            Code: PUSH1 0x1f
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
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('601f6101000a600055601f60ff0a600155601f6101010a600255')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('601f6101000a600055601f60ff0a600155601f6101010a600255'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0x0100000000000000000000000000000000000000000000000000000000000000)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x01)), 0xe2bfe95c5d7067567402dd9d7235fc088ac84eab8113bf8d7e3c288d2f1eff)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x02)), 0x0120e30c8c1bb25c9d2219ea196c17ded3d775b231bbd28005b131fa90d11f01)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 39913)

    def test_expPowerOf256Of256_25(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: expPowerOf256Of256_25.json
            sha256sum: ba80c4646a1371e93e9ecd024b52b25819963d880c6cef7a37dc515d93cc9dca
            Code: PUSH1 0x19
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
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=10000000)
    
        bytecode = unhexlify('60196101000a6101000a600055601960ff0a6101000a60015560196101010a6101000a60025560196101000a60ff0a600355601960ff0a60ff0a60045560196101010a60ff0a60055560196101000a6101010a600655601960ff0a6101010a60075560196101010a6101010a600855')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 1000000

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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('60196101000a6101000a600055601960ff0a6101000a60015560196101010a6101000a60025560196101000a60ff0a600355601960ff0a60ff0a60045560196101010a60ff0a60055560196101000a6101010a600655601960ff0a6101010a60075560196101010a6101010a600855'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x03)), 0x33085514ff7f0000000000000000000000000000000000000000000000000001)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x04)), 0x7f510dd7198cac0a92ff7ea80451838c0dfa12114c41a0ef05907397f897feff)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x05)), 0x1275e752b6aee228ecba5e9b57ef1111deff3c651e2cfbf2cccd13151f9900ff)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x06)), 0x21f7aa6aff810000000000000000000000000000000000000000000000000001)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x07)), 0x6646340ad51a03bb710caf05756b685b33c7dad62ae68d369243700ead99ff01)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x08)), 0x29d80e8060ef2221929bb18215586c742686d6860e028ca0456b443238990101)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 862312)

    def test_expPowerOf256Of256_18(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: expPowerOf256Of256_18.json
            sha256sum: 92315d900d6b1495846bfd4e53af140385e883a2af0aa67fd43a3df3a73a189e
            Code: PUSH1 0x12
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
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=10000000)
    
        bytecode = unhexlify('60126101000a6101000a600055601260ff0a6101000a60015560126101010a6101000a60025560126101000a60ff0a600355601260ff0a60ff0a60045560126101010a60ff0a60055560126101000a6101010a600655601260ff0a6101010a60075560126101010a6101010a600855')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 1000000

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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('60126101000a6101000a600055601260ff0a6101000a60015560126101010a6101000a60025560126101000a60ff0a600355601260ff0a60ff0a60045560126101010a60ff0a60055560126101000a6101010a600655601260ff0a6101010a60075560126101010a6101010a600855'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x03)), 0x698218879ec55c33085514ff7f00000000000000000000000000000000000001)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x04)), 0x8a2cbd9f40794e2205b13306f2aa0a43c60823c64b95d8601fa4f1e521ee00ff)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x05)), 0xc1b5a1e3a81da51b10d84e880f0113ff67b863ddad3faf1f4ecf413f101200ff)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x06)), 0xc9b0f000b68fb921f7aa6aff8100000000000000000000000000000000000001)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x07)), 0x410be68e49452a1fbcd863bf6e8d637f8eae4979c34c88d552afbcc20fee0101)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x08)), 0xf540cb714754b5b1eb0373833833bd7fb0ee925ce8b92962500b7a1c22120101)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 862942)

    def test_sdiv1(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: sdiv1.json
            sha256sum: d224466fd0d90938d79dddd9910147a2f173ca4444eeda966e38419edfc56fad
            Code: PUSH32 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
                  PUSH1 0x0
                  SUB
                  PUSH32 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
                  SDIV
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff6000037fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff05600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff6000037fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff05600055'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 79980)

    def test_expPowerOf256Of256_5(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: expPowerOf256Of256_5.json
            sha256sum: e52f4cbdddf85ea945200f2b9aa9ebd3c0fa2359394022c188149b9fe18a132f
            Code: PUSH1 0x5
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
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=10000000)
    
        bytecode = unhexlify('60056101000a6101000a600055600560ff0a6101000a60015560056101010a6101000a60025560056101000a60ff0a600355600560ff0a60ff0a60045560056101010a60ff0a60055560056101000a6101010a600655600560ff0a6101010a60075560056101010a6101010a600855')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 1000000

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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('60056101000a6101000a600055600560ff0a6101000a60015560056101010a6101000a60025560056101000a60ff0a600355600560ff0a60ff0a60045560056101010a60ff0a60055560056101000a6101010a600655600560ff0a6101010a60075560056101010a6101010a600855'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x03)), 0xb581ac185aad71db2d177c286929c4c22809e5dcb3085514ff7f000000000001)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x04)), 0x75789eb2a64bc971389fbd11a1e6d7abbf95ad25e23fb9aa25e73a0bfc83feff)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x05)), 0xfc403fa42ceb6a0d0d3321bd9b2d8af25b1b667f87a04f496c78168d078500ff)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x06)), 0xcec5ec213b9cb5811f6ae00428fd7b6ef5a1af39a1f7aa6aff81000000000001)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x07)), 0x70ab32233202b98d382d17713fa0be391eaf74f85ba1740c9c3238c4ed85ff01)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x08)), 0xb622672a213faa79b32185ff93a7b27a8499e48f7b032cdb4d1a70300c850101)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 864112)

    def test_signextend_BitIsNotSet(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: signextend_BitIsNotSet.json
            sha256sum: 3e15e2e67dbe83ccdcf1eee546bff42a1eeb19ca892a0fb6610002cefc5c0440
            Code: PUSH3 0x122f6a
                  PUSH1 0x0
                  SIGNEXTEND
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=10000000)
    
        bytecode = unhexlify('62122f6a60000b600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 1000000

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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('62122f6a60000b600055'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0x6a)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 979986)

    def test_add2(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: add2.json
            sha256sum: 96dfcc5838c3676c7fefeb38d582b5ef7a5af3fe6303d976f0846542ea124657
            Code: PUSH1 0x1
                  PUSH32 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
                  ADD
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('60017fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff01600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('60017fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff01600055'))
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 94988)

    def test_signextend_BigBytePlus1_2(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: signextend_BigBytePlus1_2.json
            sha256sum: 2d4f4db0b8cce0abc97e9b4a0d771f58cc4c02dd522c0a87468eefb3236d9db3
            Code: PUSH1 0xff
                  PUSH9 0xf00000000000000001
                  SIGNEXTEND
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=10000000)
    
        bytecode = unhexlify('60ff68f000000000000000010b600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 1000000

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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('60ff68f000000000000000010b600055'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0xff)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 979986)

    def test_mulmoddivByZero1(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: mulmoddivByZero1.json
            sha256sum: cf49980ff3395877d56a96edcf18b1e369b68c5d06822e8327f1c3f2ee27aa1e
            Code: PUSH1 0x0
                  PUSH1 0x1
                  PUSH1 0x0
                  MULMOD
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('60006001600009600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('60006001600009600055'))
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 94980)

    def test_sdiv_i256min(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: sdiv_i256min.json
            sha256sum: a75f354304eea0930d85934b46916213c26a7c3b17905786de6ce0d75e8b9cf0
            Code: PUSH1 0x1
                  PUSH1 0x0
                  SUB
                  PUSH32 0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
                  PUSH1 0x0
                  SUB
                  SDIV
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('60016000037f7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff60000305600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('60016000037f7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff60000305600055'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 79974)

    def test_expPowerOf256_6(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: expPowerOf256_6.json
            sha256sum: f39c9e78e0c492a5537cd763021a18d8b6cd79762a964e3103fc215e215daa38
            Code: PUSH1 0x6
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
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('60066101000a600055600660ff0a60015560066101010a600255')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('60066101000a600055600660ff0a60015560066101010a600255'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0x01000000000000)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x01)), 0xfa0eec0efa01)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x02)), 0x01060f140f0601)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 39913)

    def test_divByNonZero3(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: divByNonZero3.json
            sha256sum: 9b1768e48871638a195e9d85141a0fd5b85e3478597ff05f85ca883ccc9c83d4
            Code: PUSH1 0x1
                  PUSH1 0x1
                  DIV
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('6001600104600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('6001600104600055'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0x01)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 79986)

    def test_addmodDivByZero(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: addmodDivByZero.json
            sha256sum: 699b519167c3ca59bb214bb1cad9eacd4e3a3c0ccc9120da44602be1b67c251c
            Code: PUSH1 0x0
                  PUSH1 0x1
                  PUSH1 0x4
                  ADDMOD
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('60006001600408600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('60006001600408600055'))
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 94980)

    def test_sdiv2(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: sdiv2.json
            sha256sum: 0f21f478a11e9ec5352a0f83ef56df1d8b0115a04da8b5db731e504165d4c83e
            Code: PUSH1 0x4
                  PUSH1 0x0
                  SUB
                  PUSH1 0x2
                  PUSH1 0x0
                  SUB
                  SDIV
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('6004600003600260000305600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('6004600003600260000305600055'))
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 94974)

    def test_expPowerOf256Of256_28(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: expPowerOf256Of256_28.json
            sha256sum: 2f1ae9d4d2a53e46e60c0bbc00f15360912d71e1fed2fd41f9e6839dbffdb05e
            Code: PUSH1 0x1c
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
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=10000000)
    
        bytecode = unhexlify('601c6101000a6101000a600055601c60ff0a6101000a600155601c6101010a6101000a600255601c6101000a60ff0a600355601c60ff0a60ff0a600455601c6101010a60ff0a600555601c6101000a6101010a600655601c60ff0a6101010a600755601c6101010a6101010a600855')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 1000000

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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('601c6101000a6101000a600055601c60ff0a6101000a600155601c6101010a6101000a600255601c6101000a60ff0a600355601c60ff0a60ff0a600455601c6101010a60ff0a600555601c6101000a6101010a600655601c60ff0a6101010a600755601c6101010a6101010a600855'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x03)), 0x14ff7f0000000000000000000000000000000000000000000000000000000001)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x04)), 0xffd368e44b3f85cb81ae394c9809ca9fa2db46a83d7880a912ab6d4a87e400ff)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x05)), 0x0981ad53c19b15a94bcf0bf20235dd0da9df25f46ae635029fe2062e6c1c00ff)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x06)), 0x6aff810000000000000000000000000000000000000000000000000000000001)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x07)), 0x19df06ffa28250867006726405fbc05d43dc2f9d2f025006db089bd46be40101)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x08)), 0x243fffe3a4f2982f45055c08f379648ab886da8027a7401117a8e0b8881c0101)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 862042)

    def test_signextend_0_BigByte(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: signextend_0_BigByte.json
            sha256sum: 424909bbf0356303bb5a4abef2cb932c66fb55f2db46dd22eba088eabf61a168
            Code: PUSH32 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
                  PUSH1 0x0
                  SIGNEXTEND
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=10000000)
    
        bytecode = unhexlify('7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff60000b600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 1000000

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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff60000b600055'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 979986)

    def test_expPowerOf256_5(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: expPowerOf256_5.json
            sha256sum: 5b2e8fdcb47b11d7de771c1ac0aa386f0ba6c1a51d423d968587caeffbec6459
            Code: PUSH1 0x5
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
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('60056101000a600055600560ff0a60015560056101010a600255')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('60056101000a600055600560ff0a60015560056101010a600255'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0x010000000000)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x01)), 0xfb09f604ff)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x02)), 0x01050a0a0501)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 39913)

    def test_expPowerOf256Of256_4(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: expPowerOf256Of256_4.json
            sha256sum: 133369ae88eeb438b9672375fa4f7e3f302d7c76626e068f3a3ab0f00eb803a9
            Code: PUSH1 0x4
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
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=10000000)
    
        bytecode = unhexlify('60046101000a6101000a600055600460ff0a6101000a60015560046101010a6101000a60025560046101000a60ff0a600355600460ff0a60ff0a60045560046101010a60ff0a60055560046101000a6101010a600655600460ff0a6101010a60075560046101010a6101010a600855')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 1000000

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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('60046101000a6101000a600055600460ff0a6101000a60015560046101010a6101000a60025560046101000a60ff0a600355600460ff0a60ff0a60045560046101010a60ff0a60055560046101000a6101010a600655600460ff0a6101010a60075560046101010a6101010a600855'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x03)), 0xe6540ce46eaf70da9d644015a661e0e245b13f307cb3885514ff7f0000000001)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x04)), 0x6526b38b05a6325b80e1c84ab41dc934fd70f33f1bd0eab3d1f61a4707fc00ff)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x05)), 0xe959516cd27e5d8fd487b72db2989b3ec2ba9fb7ead41554526fe5a3040400ff)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x06)), 0xe7498a48c6ce2530bbe814ee3440c8c44fffab7ad8a277aa6aff810000000001)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x07)), 0x2dffa3e901e5a392d15b79f4193d2168147d2aa7c55870b46c3a905d03fc0101)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x08)), 0xe16ea721c96539edb4f7fb82de0dad8cccb1e7a6966a6777635f6fb908040101)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 864202)

    def test_divBoostBug(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: divBoostBug.json
            sha256sum: fe3275283df2833162d7118278032b6c1671b682b097bb88d3cb70eb054498ba
            Code: PUSH32 0x1dae6076b981dae6076b981dae6076b981dae6076b981dae6076b981dae6077
                  PUSH32 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffba
                  DIV
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('7f01dae6076b981dae6076b981dae6076b981dae6076b981dae6076b981dae60777fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffba04600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('7f01dae6076b981dae6076b981dae6076b981dae6076b981dae6076b981dae60777fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffba04600055'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0x89)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 79986)

    def test_signextend_AlmostBiggestByte(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: signextend_AlmostBiggestByte.json
            sha256sum: 9e580dec6eab6488b54f744e2622c6062312b1219c08e29b8b476d05bf0891d5
            Code: PUSH32 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe
                  PUSH32 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe
                  SIGNEXTEND
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=10000000)
    
        bytecode = unhexlify('7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0b600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 1000000

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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0b600055'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 979986)

    def test_sdiv_i256min2(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: sdiv_i256min2.json
            sha256sum: 95b85e8b02fcb9f69748a3dcbe7b84f03a2e18d02bd9f11fa6cc81696ce117e0
            Code: PUSH1 0x1
                  PUSH1 0x0
                  SUB
                  PUSH32 0x8000000000000000000000000000000000000000000000000000000000000000
                  PUSH1 0x0
                  SUB
                  SDIV
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('60016000037f800000000000000000000000000000000000000000000000000000000000000060000305600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('60016000037f800000000000000000000000000000000000000000000000000000000000000060000305600055'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0x8000000000000000000000000000000000000000000000000000000000000000)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 79974)

    def test_divByNonZero2(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: divByNonZero2.json
            sha256sum: e0063bfc165977cec03383edad0916adad5c509bfbae2d0ed1b3ee73e703e047
            Code: PUSH1 0x18
                  PUSH1 0x0
                  DIV
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('6018600004600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('6018600004600055'))
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 94986)

    def test_expPowerOf256Of256_13(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: expPowerOf256Of256_13.json
            sha256sum: 3559c513219c03d76dad5cbdfb05f1a009d416fb9b0f86317e1e02adb1a50925
            Code: PUSH1 0xd
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
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=10000000)
    
        bytecode = unhexlify('600d6101000a6101000a600055600d60ff0a6101000a600155600d6101010a6101000a600255600d6101000a60ff0a600355600d60ff0a60ff0a600455600d6101010a60ff0a600555600d6101000a6101010a600655600d60ff0a6101010a600755600d6101010a6101010a600855')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 1000000

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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('600d6101000a6101000a600055600d60ff0a6101000a600155600d6101010a6101000a600255600d6101000a60ff0a600355600d60ff0a60ff0a600455600d6101010a60ff0a600555600d6101000a6101010a600655600d60ff0a6101010a600755600d6101010a6101010a600855'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x03)), 0xe02639036c698218879ec55c33085514ff7f0000000000000000000000000001)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x04)), 0x8be664bde946d939ce551b948b503787942d2a7734509288c1b62fd5c48bfeff)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x05)), 0xa923a28e7a75aef26c51580ffc686879e4a0b404b089bdbcd751d88b478d00ff)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x06)), 0x41ac5ea30fc9b0f000b68fb921f7aa6aff810000000000000000000000000001)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x07)), 0x0daa3a177ec975cb69bb4acf4a6e1be7bcc1ad33d1ffad97510f9fea9d8dff01)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x08)), 0x19e6822beb889be28310060f4fb9741bfd50a31fa81ec65de21f7b02548d0101)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 863392)

    def test_mulmod4(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: mulmod4.json
            sha256sum: 31c06c40acc8ab37bb205e24939f1bd09a7e65eac4e3976f5ca436b07af2f3cc
            Code: PUSH1 0x64
                  PUSH1 0x1b
                  PUSH1 0x25
                  MULMOD
                  PUSH1 0x0
                  MSTORE8
                  PUSH1 0x0
                  PUSH1 0x1
                  RETURN
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('6064601b60250960005360006001f3')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('6064601b60250960005360006001f3'))
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 99968)

    def test_smod0(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: smod0.json
            sha256sum: ff6e79c3ee961d27ad631ec3234dbe27f60d5b9cd7a7680387dea3e297f0f3a0
            Code: PUSH1 0x3
                  PUSH1 0x0
                  SUB
                  PUSH1 0x5
                  PUSH1 0x0
                  SUB
                  SMOD
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('6003600003600560000307600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('6003600003600560000307600055'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 79974)

    def test_expPowerOf256Of256_24(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: expPowerOf256Of256_24.json
            sha256sum: a6e5372e634098106ecb26b9450645cf2f57b9cf067a90f3863dc9ab21d88b50
            Code: PUSH1 0x18
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
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=10000000)
    
        bytecode = unhexlify('60186101000a6101000a600055601860ff0a6101000a60015560186101010a6101000a60025560186101000a60ff0a600355601860ff0a60ff0a60045560186101010a60ff0a60055560186101000a6101010a600655601860ff0a6101010a60075560186101010a6101010a600855')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 1000000

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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('60186101000a6101000a600055601860ff0a6101000a60015560186101010a6101000a60025560186101000a60ff0a600355601860ff0a60ff0a60045560186101010a60ff0a60055560186101000a6101010a600655601860ff0a6101010a60075560186101010a6101010a600855'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x03)), 0x5c33085514ff7f00000000000000000000000000000000000000000000000001)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x04)), 0xd542e526003539ead104274aff2d78332366e29d328c2161f0c120731fe800ff)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x05)), 0xc706cb25e8384ce9bb5c9cb48415238ba03e16c448e292c0a101843b081800ff)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x06)), 0xb921f7aa6aff8100000000000000000000000000000000000000000000000001)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x07)), 0x4ca55f89202c524cb0f1cb3195d13c8d94a9f7a05c59e1d4031577c707e80101)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x08)), 0x8c4b0574e9156b80035f3ecdcf1fe79d273ed7559747a4322bcd338f20180101)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 862402)

    def test_mulmoddivByZero2(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: mulmoddivByZero2.json
            sha256sum: b5ecff08a9253fd2c07fe2355faafe42448e83131c0844f820dc30bc9aa5f3a3
            Code: PUSH1 0x0
                  PUSH1 0x0
                  PUSH1 0x1
                  MULMOD
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('60006000600109600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('60006000600109600055'))
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 94980)

    def test_sub0(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: sub0.json
            sha256sum: e185a37296e08e7dec9a4f77e22663970f19de5a3c25fb0061df02a0743b1d05
            Code: PUSH1 0x1
                  PUSH1 0x17
                  SUB
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('6001601703600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('6001601703600055'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0x16)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 79988)

    def test_mulmoddivByZero(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: mulmoddivByZero.json
            sha256sum: 70d6b833c9c91d9a01e43a01b248a4a5a63d2e333a73122ab602d690de9cc34a
            Code: PUSH1 0x0
                  PUSH1 0x1
                  PUSH1 0x5
                  MULMOD
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('60006001600509600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('60006001600509600055'))
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 94980)

    def test_mulmod2(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: mulmod2.json
            sha256sum: 6e8dc3cc2c5f0a7eb90d7aaa90a0253d7062c6e750554e6a44f1d711115ebb34
            Code: PUSH1 0x3
                  PUSH1 0x1
                  PUSH1 0x5
                  PUSH1 0x0
                  SUB
                  MULMOD
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('60036001600560000309600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('60036001600560000309600055'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0x02)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 79974)

    def test_expPowerOf256Of256_1(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: expPowerOf256Of256_1.json
            sha256sum: 55ea9d8a3710b200e38f83bbb9622171a99c9d85410b39f0fc319cade6d25913
            Code: PUSH1 0x1
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
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=10000000)
    
        bytecode = unhexlify('60016101000a6101000a600055600160ff0a6101000a60015560016101010a6101000a60025560016101000a60ff0a600355600160ff0a60ff0a60045560016101010a60ff0a60055560016101000a6101010a600655600160ff0a6101010a60075560016101010a6101010a600855')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 1000000

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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('60016101000a6101000a600055600160ff0a6101000a60015560016101010a6101000a60025560016101000a60ff0a600355600160ff0a60ff0a60045560016101010a60ff0a60055560016101000a6101010a600655600160ff0a6101010a60075560016101010a6101010a600855'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x03)), 0x06c3acd330b959ad6efabce6d2d2125e73a88a65a9880d203dddf5957f7f0001)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x04)), 0x8f965a06da0ac41dcb3a34f1d8ab7d8fee620a94faa42c395997756b007ffeff)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x05)), 0xbce9265d88a053c18bc229ebff404c1534e1db43de85131da0179fe9ff8100ff)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x06)), 0x02b5e9d7a094c19f5ebdd4f2e618f859ed15e4f1f0351f286bf849eb7f810001)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x07)), 0xc73b7a6f68385c653a24993bb72eea0e4ba17470816ec658cf9c5bedfd81ff01)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x08)), 0xb89fc178355660fe1c92c7d8ff11524702fad6e2255447946442356b00810101)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 864472)

    def test_expPowerOf256Of256_11(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: expPowerOf256Of256_11.json
            sha256sum: c095d37a7b0eb417879abbe3066683a970ac925a68661ac9908ad4f16c9774c4
            Code: PUSH1 0xb
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
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=10000000)
    
        bytecode = unhexlify('600b6101000a6101000a600055600b60ff0a6101000a600155600b6101010a6101000a600255600b6101000a60ff0a600355600b60ff0a60ff0a600455600b6101010a60ff0a600555600b6101000a6101010a600655600b60ff0a6101010a600755600b6101010a6101010a600855')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 1000000

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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('600b6101000a6101000a600055600b60ff0a6101000a600155600b6101010a6101000a600255600b6101000a60ff0a600355600b60ff0a60ff0a600455600b6101010a60ff0a600555600b6101000a6101010a600655600b60ff0a6101010a600755600b6101010a6101010a600855'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x03)), 0xe1440264b8ee0cea0218879ec55c33085514ff7f000000000000000000000001)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x04)), 0x29575fdce377b23043e489e358581474bc863187fa85f9945473a2be5889feff)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x05)), 0x3df8c030ec521fb109c4d887dbbc14c7c9c9921b27058e3503971b60b18b00ff)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x06)), 0x67799740340daf4a30f000b68fb921f7aa6aff81000000000000000000000001)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x07)), 0x540a4e4635b40585e09ff10b63ffe310dd717fca5c0a51570091e25e378bff01)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x08)), 0xdbbaef5c49ffee61b08cde6ebc8dba6e9a62d56c2355d1980cb9e790bc8b0101)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 863572)

    def test_addmod1_overflow3(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: addmod1_overflow3.json
            sha256sum: dcf46135e92be5e31ad5395de44fdce8d6c44c2a594712ebd9c6c79b560efef4
            Code: PUSH1 0x5
                  PUSH1 0x1
                  PUSH1 0x1
                  PUSH1 0x0
                  SUB
                  ADDMOD
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('60056001600160000308600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 1000000

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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('60056001600160000308600055'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0x01)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 979974)

    def test_exp4(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: exp4.json
            sha256sum: b0afd80d0882556ef89a57269e89616dd8f3eb5b0b97c5c2505f36415fc643cd
            Code: PUSH1 0x0
                  PUSH4 0x7fffffff
                  EXP
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('6000637fffffff0a600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('6000637fffffff0a600055'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0x01)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 79981)

    def test_expPowerOf256_29(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: expPowerOf256_29.json
            sha256sum: 7002014dfffb7c97759aab32cc66a6a0017742354d0df30b3189c553ef2a09a3
            Code: PUSH1 0x1d
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
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('601d6101000a600055601d60ff0a600155601d6101010a600255')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('601d6101000a600055601d60ff0a600155601d6101010a600255'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0x010000000000000000000000000000000000000000000000000000000000)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x01)), 0xe48814fe44fc1a8f78642d946d7c879b39a055b6988e438647446a1cff)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x02)), 0x011ea4a49e3a9ee435d23f98a8826a875a9ae54cb3090d5c3fd547961d01)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 39913)

    def test_mul5(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: mul5.json
            sha256sum: 27e7f51bca0b7069694d12c59d43003cef22ec0ecf0309aa28ec47ca3911db95
            Code: PUSH32 0x8000000000000000000000000000000000000000000000000000000000000000
                  PUSH32 0x8000000000000000000000000000000000000000000000000000000000000000
                  MUL
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('7f80000000000000000000000000000000000000000000000000000000000000007f800000000000000000000000000000000000000000000000000000000000000002600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('7f80000000000000000000000000000000000000000000000000000000000000007f800000000000000000000000000000000000000000000000000000000000000002600055'))
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 94986)

    def test_expPowerOf256_32(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: expPowerOf256_32.json
            sha256sum: b44ae8df0e423ad89f67faa99b4a982ee5bf923f0f585a35cec69259f6f8fa71
            Code: PUSH1 0x20
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
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('60206101000a600055602060ff0a60015560206101010a600255')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('60206101000a600055602060ff0a60015560206101010a600255'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x01)), 0xe1dd29730112f6ef1d8edabfd4c3c60c823d865cd592abcdf0bdec64a1efe001)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x02)), 0x2203ef98a7ce0ef9bf3c04038583f6b2ab4d27e3ed8e5285b6e32c8b61f02001)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 54913)

    def test_expPowerOf256Of256_7(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: expPowerOf256Of256_7.json
            sha256sum: b138bd8537c0d2aeab0e2b0ef55017e320bfc2fd2102d283e38a983bd30bd064
            Code: PUSH1 0x7
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
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=10000000)
    
        bytecode = unhexlify('60076101000a6101000a600055600760ff0a6101000a60015560076101010a6101000a60025560076101000a60ff0a600355600760ff0a60ff0a60045560076101010a60ff0a60055560076101000a6101010a600655600760ff0a6101010a60075560076101010a6101010a600855')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 1000000

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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('60076101000a6101000a600055600760ff0a6101000a60015560076101010a6101000a60025560076101000a60ff0a600355600760ff0a60ff0a60045560076101010a60ff0a60055560076101000a6101010a600655600760ff0a6101010a60075560076101010a6101010a600855'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x03)), 0x8bb02654111ad8c60ad8af132283a81f455c33085514ff7f0000000000000001)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x04)), 0xa8f75c129dbb8466d6703a2a0b8212131b3248d70e2478862ac40fe17485feff)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x05)), 0x5fd4d2de580383ee59f5e800ddb3f1717ceae03aede19d3dec5e5a69918700ff)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x06)), 0xc8624230b524b85d6340da48a5db20370fb921f7aa6aff810000000000000001)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x07)), 0x287b58a5a13cd7f454468ca616c181712f5ed25433a7d5a894b6ced35f87ff01)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x08)), 0x09930d11ac2804fa977bf951593c8dff8498779cc0cdc5812a4fba2f98870101)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 863932)

    def test_expPowerOf256Of256_23(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: expPowerOf256Of256_23.json
            sha256sum: f07022f79f143cb93c4ec3883ae3438038e6945295ec29f1f268e95a90e19fca
            Code: PUSH1 0x17
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
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=10000000)
    
        bytecode = unhexlify('60176101000a6101000a600055601760ff0a6101000a60015560176101010a6101000a60025560176101000a60ff0a600355601760ff0a60ff0a60045560176101010a60ff0a60055560176101000a6101010a600655601760ff0a6101010a60075560176101010a6101010a600855')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 1000000

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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('60176101000a6101000a600055601760ff0a6101000a60015560176101010a6101000a60025560176101000a60ff0a600355601760ff0a60ff0a60045560176101010a60ff0a60055560176101000a6101010a600655601760ff0a6101010a60075560176101010a6101010a600855'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x03)), 0xc55c33085514ff7f000000000000000000000000000000000000000000000001)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x04)), 0x537ca0f03f974303005f1e6693b55b72315a166841732e42b8353724a495feff)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x05)), 0x86418797ec60058de6cca47dfdbee79923ac49d7801e01840041ca76719700ff)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x06)), 0x8fb921f7aa6aff81000000000000000000000000000000000000000000000001)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x07)), 0x56a55341ab8d4318f1cfb55d5f21e2ba35d7e070a72bac6b2b21baae5f97ff01)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x08)), 0x55ddd0ec77909de6d8311116cf520398e816f928b06fdd90ec239d0488970101)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 862492)

    def test_smod_i256min1(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: smod_i256min1.json
            sha256sum: 4fab8396013a69a2e27b500d1eafc17724e7d1746a336264f1ebfd3c16ea41e9
            Code: PUSH1 0x1
                  PUSH1 0x0
                  SUB
                  PUSH32 0x8000000000000000000000000000000000000000000000000000000000000000
                  PUSH1 0x0
                  SUB
                  SMOD
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('60016000037f800000000000000000000000000000000000000000000000000000000000000060000307600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('60016000037f800000000000000000000000000000000000000000000000000000000000000060000307600055'))
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 94974)

    def test_smod_i256min2(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: smod_i256min2.json
            sha256sum: e4e1b0c5b6cb075722450891a8021b351ef372c6cd0ac462eabe87f7527f8ac6
            Code: PUSH1 0x1
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
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('600160016000037f80000000000000000000000000000000000000000000000000000000000000006000030703600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('600160016000037f80000000000000000000000000000000000000000000000000000000000000006000030703600055'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 79968)

    def test_smod7(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: smod7.json
            sha256sum: f994b29e003918f15520608025e571d08363b39a2f028a5c1ab6cc9121484c01
            Code: PUSH32 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
                  PUSH32 0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
                  PUSH1 0x0
                  SUB
                  SMOD
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7f7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff60000307600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 10000

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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7f7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff60000307600055'))
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 4980)

    def test_expPowerOf256Of256_31(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: expPowerOf256Of256_31.json
            sha256sum: 8d4c69f622e12025ff763880fb81489d2816dd996e567a6fbca9af447c939b46
            Code: PUSH1 0x1f
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
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=10000000)
    
        bytecode = unhexlify('601f6101000a6101000a600055601f60ff0a6101000a600155601f6101010a6101000a600255601f6101000a60ff0a600355601f60ff0a60ff0a600455601f6101010a60ff0a600555601f6101000a6101010a600655601f60ff0a6101010a600755601f6101010a6101010a600855')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 1000000

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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('601f6101000a6101000a600055601f60ff0a6101000a600155601f6101010a6101000a600255601f6101000a60ff0a600355601f60ff0a60ff0a600455601f6101010a60ff0a600555601f6101000a6101010a600655601f60ff0a6101010a600755601f6101010a6101010a600855'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x03)), 0x01)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x04)), 0xf9cb87f5b1ab58602f52a1e9d392e5675b86a59a53943a8d4ec2a915dc9dfeff)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x05)), 0x893d729a64e318860ec5047e70e598da163eb41e71e74b04dfd4712d419f00ff)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x06)), 0x01)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x07)), 0xee5f2839c1b4f6ca05e6fdb04e2fb49c0f860b3765c27dc781a150cb7f9fff01)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x08)), 0xb4c358e3c6bcddfb509ea487d733df0e1854f29c3b6bfd4a8caabe3f609f0101)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 861772)

    def test_mul2(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: mul2.json
            sha256sum: ded58f693df18ced862fde46ba5b800217564648c15f2c6ec9c09545ba9d454b
            Code: PUSH1 0x17
                  PUSH1 0x0
                  MUL
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('6017600002600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('6017600002600055'))
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 94986)

    def test_addmod1(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: addmod1.json
            sha256sum: 9e7cb74d28005ca4b84e66485c95a896c62a3605a453e37eb15e287c8be7d942
            Code: PUSH1 0x2
                  PUSH1 0x2
                  PUSH1 0x0
                  SUB
                  PUSH1 0x1
                  PUSH1 0x0
                  SUB
                  ADDMOD
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('60026002600003600160000308600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('60026002600003600160000308600055'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0x01)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 79968)

    def test_expPowerOf256Of256_15(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: expPowerOf256Of256_15.json
            sha256sum: 6ba6936af4d67ffb437014aa5d698d8f372d3be932fc1b262b9b9506c36508ac
            Code: PUSH1 0xf
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
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=10000000)
    
        bytecode = unhexlify('600f6101000a6101000a600055600f60ff0a6101000a600155600f6101010a6101000a600255600f6101000a60ff0a600355600f60ff0a60ff0a600455600f6101010a60ff0a600555600f6101000a6101010a600655600f60ff0a6101010a600755600f6101010a6101010a600855')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 1000000

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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('600f6101000a6101000a600055600f60ff0a6101000a600155600f6101010a6101000a600255600f6101000a60ff0a600355600f60ff0a60ff0a600455600f6101010a60ff0a600555600f6101000a6101010a600655600f60ff0a6101010a600755600f6101010a6101010a600855'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x03)), 0x9882ec698218879ec55c33085514ff7f00000000000000000000000000000001)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x04)), 0x75c4915e18b96704209738f5ca765568bb4dc4113d56683977825a132c8dfeff)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x05)), 0x5c76839bf5a80b1da705dbdf43e4dd6770cd7501af11ff2dab7918dfe18f00ff)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x06)), 0xbf228fc9b0f000b68fb921f7aa6aff8100000000000000000000000000000001)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x07)), 0xc6a29131e7594004bc2aa79f0d2c402a1409c57c77d284c14b1a3ab0ff8fff01)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x08)), 0xe6b3e5cf6ec90e532fef7d08455ebf92a03e9e3f6e224ea0febdf1a9f08f0101)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 863212)

    def test_expPowerOf2_16(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: expPowerOf2_16.json
            sha256sum: 2c3a71539fc95229e67a05630611ee85e45c8441f0d517da8a25d68b873da3f0
            Code: PUSH1 0x10
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
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('601060020a600055600f60020a600155601160020a600255')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('601060020a600055600f60020a600155601160020a600255'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0x010000)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x01)), 0x8000)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x02)), 0x020000)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 39913)

    def test_expPowerOf256Of256_2(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: expPowerOf256Of256_2.json
            sha256sum: cde732ffd8858cd61f0586632164327d840f78943df0821504ca9be92766d243
            Code: PUSH1 0x2
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
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=10000000)
    
        bytecode = unhexlify('60026101000a6101000a600055600260ff0a6101000a60015560026101010a6101000a60025560026101000a60ff0a600355600260ff0a60ff0a60045560026101010a60ff0a60055560026101000a6101010a600655600260ff0a6101010a60075560026101010a6101010a600855')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 1000000

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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('60026101000a6101000a600055600260ff0a6101000a60015560026101010a6101000a60025560026101000a60ff0a600355600260ff0a60ff0a60045560026101010a60ff0a60055560026101000a6101010a600655600260ff0a6101010a60075560026101010a6101010a600855'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x03)), 0x4ee4ceeaac565c81f55a87c43f82f7c889ef4fc7c679671e28d594ff7f000001)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x04)), 0x82f46a1b4e34d66712910615d2571d75606ceac51fa8ca8c58cf6ca881fe00ff)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x05)), 0x81c9fcefa5de158ae2007f25d35c0d11cd735342a48905955a5a6852800200ff)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x06)), 0x666ac362902470ed850709e2a29969d10cba09debc03c38d172aeaff81000001)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x07)), 0xeb30a3c678a01bde914548f98f3366dc0ffe9f85384ebf1111d03dad7ffe0101)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x08)), 0x72d0a7939b6303ce1d46e6e3f1b8be303bfdb2b00f41ad8076b0975782020101)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 864382)

    def test_fibbonacci_unrolled(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: fibbonacci_unrolled.json
            sha256sum: 96a4a7bcd1eed854a2d0778c706de18fb99bcd359834fe818b6eaed74afc3dcd
            Code: PUSH1 0x1
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
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=10000000)
    
        bytecode = unhexlify('6001600181810181810181810181810181810181810181810181810181810181810181810181810181810181810181810181810181810160005260206000f3')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 1000000

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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('6001600181810181810181810181810181810181810181810181810181810181810181810181810181810181810181810181810181810160005260206000f3'))
        #check outs
        self.assertEqual(returndata, unhexlify('0000000000000000000000000000000000000000000000000000000000001055'))
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 999826)

    def test_mulmod1_overflow(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: mulmod1_overflow.json
            sha256sum: 12d71b58080463465d8822d3b6629037f70dd2f8724cc2f287c7e3c8e31ee88f
            Code: PUSH1 0x5
                  PUSH1 0x2
                  PUSH1 0x1
                  PUSH1 0x0
                  SUB
                  MULMOD
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('60056002600160000309600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 10000

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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('60056002600160000309600055'))
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 4974)

    def test_mulUnderFlow(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: mulUnderFlow.json
            sha256sum: 07f33220f500f3cff0eb048aa153f3b56b5442c84a28b3c893559d7aa6d57769
            Code: PUSH1 0x1
                  MUL
                  PUSH1 0x1
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('600102600155')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
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

    def test_signextend_bitIsSet(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: signextend_bitIsSet.json
            sha256sum: c763feca37e8b16e1187232879fc3fc7fad7c4c5b0c22e2098bfc90fc708a2b4
            Code: PUSH3 0x122ff4
                  PUSH1 0x0
                  SIGNEXTEND
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=10000000)
    
        bytecode = unhexlify('62122ff460000b600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 1000000

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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('62122ff460000b600055'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff4)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 979986)

    def test_divByZero_2(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: divByZero_2.json
            sha256sum: 2d0cd8a2e436a23eae21777e1eed26d4a93c95f3ab2acb277b159d7239b4c36c
            Code: PUSH1 0x7
                  PUSH1 0x0
                  PUSH1 0xd
                  DIV
                  ADD
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('60076000600d0401600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('60076000600d0401600055'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0x07)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 79980)

    def test_expPowerOf256Of256_14(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: expPowerOf256Of256_14.json
            sha256sum: 771926f9010806c01969e395afd82b9dc72e0436d9c229a055ab772d5bee6ca7
            Code: PUSH1 0xe
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
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=10000000)
    
        bytecode = unhexlify('600e6101000a6101000a600055600e60ff0a6101000a600155600e6101010a6101000a600255600e6101000a60ff0a600355600e60ff0a60ff0a600455600e6101010a60ff0a600555600e6101000a6101010a600655600e60ff0a6101010a600755600e6101010a6101010a600855')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 1000000

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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('600e6101000a6101000a600055600e60ff0a6101000a600155600e6101010a6101000a600255600e6101000a60ff0a600355600e60ff0a60ff0a600455600e6101010a60ff0a600555600e6101000a6101010a600655600e60ff0a6101010a600755600e6101010a6101010a600855'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x03)), 0xdb9902ec698218879ec55c33085514ff7f000000000000000000000000000001)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x04)), 0x83fab06c6c8fef761ebbb9534c06ac2a9d61820623008069062ff3b1e1f200ff)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x05)), 0x3f791dd183ed5b963bd86e0dba1a9dd5b8ceeb078f15c73062f1942fd40e00ff)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x06)), 0xe0bfa28fc9b0f000b68fb921f7aa6aff81000000000000000000000000000001)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x07)), 0x8133b760dfae27560eb490f235ddfa301f058dee4f01f3fe4b3567d0d3f20101)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x08)), 0xcd4cd0124e983af71620fb5f98275965c6a8bebc4b8adc288b63224ee20e0101)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 863302)

    def test_expPowerOf2_128(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: expPowerOf2_128.json
            sha256sum: d769c6a75d99975be8e86784d56d45d33ff36eeba52f7a238daa12e84ffa854b
            Code: PUSH1 0x80
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
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('608060020a600055607f60020a600155608160020a600255')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('608060020a600055607f60020a600155608160020a600255'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0x0100000000000000000000000000000000)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x01)), 0x80000000000000000000000000000000)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x02)), 0x0200000000000000000000000000000000)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 39913)

    def test_sdiv7(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: sdiv7.json
            sha256sum: b097c73bc2c4c5f2329abef383205580973442668673b6fb6feccd151c866c39
            Code: PUSH1 0x19
                  PUSH1 0x1
                  PUSH1 0x0
                  SUB
                  SDIV
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('6019600160000305600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('6019600160000305600055'))
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 94980)

    def test_sdiv_i256min3(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: sdiv_i256min3.json
            sha256sum: 353f04f71f36a087f355ba9def055b57d53c65fcb2ebb9890dee44ffd6f0e105
            Code: PUSH32 0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
                  PUSH1 0x0
                  SUB
                  PUSH32 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
                  SDIV
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('7f7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff6000037fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff05600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x1
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 1000000

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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('7f7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff6000037fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff05600055'))
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 994980)

    def test_sdiv3(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: sdiv3.json
            sha256sum: 0d4372b97497489fdb38dc01e5b03d73e20d29b57d638564d6e54d87c4dbd46f
            Code: PUSH1 0x2
                  PUSH1 0x0
                  SUB
                  PUSH1 0x4
                  SDIV
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('6002600003600405600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('6002600003600405600055'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 79980)

    def test_expPowerOf256Of256_16(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: expPowerOf256Of256_16.json
            sha256sum: 5acb81a90afe62bab2a068d166ab7e0d77fdf71db887357486eaa57be2097585
            Code: PUSH1 0x10
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
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=10000000)
    
        bytecode = unhexlify('60106101000a6101000a600055601060ff0a6101000a60015560106101010a6101000a60025560106101000a60ff0a600355601060ff0a60ff0a60045560106101010a60ff0a60055560106101000a6101010a600655601060ff0a6101010a60075560106101010a6101010a600855')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 1000000

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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('60106101000a6101000a600055601060ff0a6101000a60015560106101010a6101000a60025560106101000a60ff0a600355601060ff0a60ff0a60045560106101010a60ff0a60055560106101000a6101010a600655601060ff0a6101010a60075560106101010a6101010a600855'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x03)), 0x82ec698218879ec55c33085514ff7f0000000000000000000000000000000001)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x04)), 0x3122f4bcdf6dd8b265cd18eb6af28c879aed44a35e0bf59273e39e6c7ff000ff)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x05)), 0x6a2b3bc87a02c29b9d27757df43047ecd0f15485270fca27417a701c701000ff)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x06)), 0x228fc9b0f000b68fb921f7aa6aff810000000000000000000000000000000001)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x07)), 0x88e1259502eef93d46060aacc9e2ff506c734dade0b6714ab12d17e46ff00101)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x08)), 0x4a103813c12c12169b218296bb0a9eae80cf8d2b158aa70eb990f99480100101)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 863122)

    def test_expPowerOf256_2(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: expPowerOf256_2.json
            sha256sum: b012e7ef19b7246c611040efe1cd4c02a0011c48749337388f0c59d2a3679a08
            Code: PUSH1 0x2
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
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('60026101000a600055600260ff0a60015560026101010a600255')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('60026101000a600055600260ff0a60015560026101010a600255'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0x010000)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x01)), 0xfe01)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x02)), 0x010201)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 39913)

    def test_expPowerOf2_32(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: expPowerOf2_32.json
            sha256sum: 1ca89c3edda3c9290247d3da6f3a3b03037059a015b70973ee54d690913bef25
            Code: PUSH1 0x20
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
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('602060020a600055601f60020a600155602160020a600255')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('602060020a600055601f60020a600155602160020a600255'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0x0100000000)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x01)), 0x80000000)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x02)), 0x0200000000)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 39913)

    def test_signextend_BigByteBigByte(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: signextend_BigByteBigByte.json
            sha256sum: 75518a6c534f0b47b7217ca634c45f8deec9c202c789d0055e91769e3d59527c
            Code: PUSH32 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
                  PUSH32 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
                  SIGNEXTEND
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=10000000)
    
        bytecode = unhexlify('7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0b600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 1000000

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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0b600055'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 979986)

    def test_expPowerOf256_19(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: expPowerOf256_19.json
            sha256sum: 0cc1c1acafa265d5699e932898535330a4ae5a7da33df446d3de1bc9b8f4111e
            Code: PUSH1 0x13
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
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('60136101000a600055601360ff0a60015560136101010a600255')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('60136101000a600055601360ff0a60015560136101010a600255'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0x0100000000000000000000000000000000000000)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x01)), 0xeda745f6fd3851d68db3866a315cdfc85512ff)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x02)), 0x0113aed851d6c1fca84402033e297b27c9ab1301)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 39913)

    def test_mulmod1_overflow2(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: mulmod1_overflow2.json
            sha256sum: 9361ad1f015dcd2ff73fc319d3615689948a8cff5b1d693cbcb23b992a1f90db
            Code: PUSH1 0x5
                  PUSH1 0x2
                  PUSH32 0x8000000000000000000000000000000000000000000000000000000000000000
                  MULMOD
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('600560027f800000000000000000000000000000000000000000000000000000000000000009600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 1000000

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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('600560027f800000000000000000000000000000000000000000000000000000000000000009600055'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0x01)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 979980)

    def test_smod6(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: smod6.json
            sha256sum: abeb4b71ca1ccd7c9974d0a121c211ceb82091231ce00c38e93832c1fa0b38af
            Code: PUSH32 0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
                  PUSH32 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
                  PUSH1 0x0
                  SUB
                  SMOD
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('7f7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff60000307600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('7f7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff60000307600055'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0x01)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 79980)

    def test_addmod2_0(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: addmod2_0.json
            sha256sum: bbf4dffad9e7377fa52c268f04c35b73067d116100ee6e3e063af74e5114c8a0
            Code: PUSH1 0x3
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
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('60036001600660000308600360056000030714600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('60036001600660000308600360056000030714600055'))
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 94954)

    def test_expXY_success(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: expXY_success.json
            sha256sum: a9d554c77e7cbb0bf5374f68f128fe84f896bb0996e3fc56d935fcc3d243a0e4
            Code: PUSH1 0x0
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
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('6000356000556020356001556001546000540a600255')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = unhexlify('0000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000f')
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('6000356000556020356001556001546000540a600255'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0x02)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x01)), 0x0f)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x02)), 0x8000)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 39853)

    def test_smod5(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: smod5.json
            sha256sum: 7d01d4c43ccc6c8229f960244f07169118613c9a3d6112a1b602695f4c6d3132
            Code: PUSH32 0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
                  PUSH32 0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
                  PUSH1 0x0
                  SUB
                  SMOD
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('7f7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7f7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff60000307600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 10000

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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('7f7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7f7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff60000307600055'))
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 4980)

    def test_expPowerOf256_25(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: expPowerOf256_25.json
            sha256sum: 55f40ba018ea3e5a3c2a3033c1261e54e2ff042f2d3c9561fffecdf650f081c0
            Code: PUSH1 0x19
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
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('60196101000a600055601960ff0a60015560196101010a600255')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('60196101000a600055601960ff0a60015560196101010a600255'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0x0100000000000000000000000000000000000000000000000000)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x01)), 0xe823349d2286a5ec3de3529625f683e56c0903589efad418ff)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x02)), 0x011a352e3c45325c4583eb6149e1b7d4e73f709bbb72fd2c1901)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 39913)

    def test_mul6(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: mul6.json
            sha256sum: da2592cf38ec886ab0db85c44bffe2d200dc276fc6ff595ee4c012304e96c496
            Code: PUSH32 0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
                  PUSH32 0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
                  MUL
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('7f7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7f7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff02600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('7f7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7f7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff02600055'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0x01)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 79986)

    def test_div1(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: div1.json
            sha256sum: 9a5f11688d430e2cb5f9b54e4a4cd6ff8ab60e7507cd3aed74f906c844a9510b
            Code: PUSH1 0x2
                  PUSH32 0xfedcba9876543210fedcba9876543210fedcba9876543210fedcba9876543210
                  DIV
                  PUSH1 0x0
                  MSTORE
                  PUSH1 0x20
                  PUSH1 0x0
                  RETURN
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('60027ffedcba9876543210fedcba9876543210fedcba9876543210fedcba98765432100460005260206000f3')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('60027ffedcba9876543210fedcba9876543210fedcba9876543210fedcba98765432100460005260206000f3'))
        #check outs
        self.assertEqual(returndata, unhexlify('7f6e5d4c3b2a19087f6e5d4c3b2a19087f6e5d4c3b2a19087f6e5d4c3b2a1908'))
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 99974)

    def test_expPowerOf256Of256_21(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: expPowerOf256Of256_21.json
            sha256sum: 133b198b7d5f401a7c9e8f06f60743ed28a5fd8bf385d818423fd2c634b10e86
            Code: PUSH1 0x15
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
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=10000000)
    
        bytecode = unhexlify('60156101000a6101000a600055601560ff0a6101000a60015560156101010a6101000a60025560156101000a60ff0a600355601560ff0a60ff0a60045560156101010a60ff0a60055560156101000a6101010a600655601560ff0a6101010a60075560156101010a6101010a600855')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 1000000

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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('60156101000a6101000a600055601560ff0a6101000a60015560156101010a6101000a60025560156101000a60ff0a600355601560ff0a60ff0a60045560156101010a60ff0a60055560156101000a6101010a600655601560ff0a6101010a60075560156101010a6101010a600855'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x03)), 0x879ec55c33085514ff7f00000000000000000000000000000000000000000001)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x04)), 0x7fd07055ff50cdfe4b4bd9a15133d72d3607d92eb7ac81bac93db7ff4c93feff)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x05)), 0x665ac5c769e87f61d5993abc26522fbfca2734d76a63216b2d550d29c79500ff)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x06)), 0xb68fb921f7aa6aff8100000000000000000000000000000000000000000001)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x07)), 0x1c93db67c9884bc694686d69a25a5d7ed089841d5ce147fdd7199ab00d95ff01)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x08)), 0x485053d8ff66be52036597520344fac87b6a305426a9e49221d3f934dc950101)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 862672)

    def test_expPowerOf256Of256_20(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: expPowerOf256Of256_20.json
            sha256sum: 773b8ea18b482afbe1c50d8c7fcb12789d399fa1e316d72319f653e8150c7f7e
            Code: PUSH1 0x14
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
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=10000000)
    
        bytecode = unhexlify('60146101000a6101000a600055601460ff0a6101000a60015560146101010a6101000a60025560146101000a60ff0a600355601460ff0a60ff0a60045560146101010a60ff0a60055560146101000a6101010a600655601460ff0a6101010a60075560146101010a6101010a600855')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 1000000

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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('60146101000a6101000a600055601460ff0a6101000a60015560146101010a6101000a60025560146101000a60ff0a600355601460ff0a60ff0a60045560146101010a60ff0a60055560146101000a6101010a600655601460ff0a6101010a60075560146101010a6101010a600855'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x03)), 0x18879ec55c33085514ff7f000000000000000000000000000000000000000001)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x04)), 0x67e4797dc21f02ce4a7c52218c7dbea5d212e6c244e24f0ba4c08613c7ec00ff)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x05)), 0xa1ce1a085f258785846939cc1d2e8725ac94ad4dff8913234e00679fb41400ff)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x06)), 0xf000b68fb921f7aa6aff81000000000000000000000000000000000000000001)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x07)), 0xcce501857a1cb45473915a28082af950e0f78f7e2de68ce748adb661b3ec0101)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x08)), 0x3b2e28d274a16c08b58a23bad63bba6d7b09685769d1f68ca3873bedc8140101)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 862762)

    def test_mulmod3(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: mulmod3.json
            sha256sum: 0251e3f2116b47183a5c072b9b2194a133ed124ec402ec38e9b804e6372b293b
            Code: PUSH1 0x3
                  PUSH1 0x0
                  SUB
                  PUSH1 0x1
                  PUSH1 0x5
                  MULMOD
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('60036000036001600509600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('60036000036001600509600055'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0x05)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 79974)

    def test_mulmod1_overflow3(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: mulmod1_overflow3.json
            sha256sum: e626164ad7fe44a9b5d88a3f65b2abb79843fb4e497c9f38f617045575d83a21
            Code: PUSH1 0x5
                  PUSH1 0x2
                  PUSH32 0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
                  MULMOD
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('600560027f7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff09600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 1000000

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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('600560027f7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff09600055'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0x04)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 979980)

    def test_sub1(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: sub1.json
            sha256sum: 738dccff9466ec1fc4f88b7e7387cba994042be68f37e47ffd3bef90d5e360cd
            Code: PUSH1 0x3
                  PUSH1 0x2
                  SUB
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('6003600203600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('6003600203600055'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 79988)

    def test_sdiv6(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: sdiv6.json
            sha256sum: 391a875666f18ddd1d4bfedc31e6460f696d40698ff1ddeb6b52f9454cff0ba7
            Code: PUSH1 0x0
                  PUSH32 0x8000000000000000000000000000000000000000000000000000000000000000
                  PUSH1 0x0
                  SUB
                  SDIV
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('60007f800000000000000000000000000000000000000000000000000000000000000060000305600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('60007f800000000000000000000000000000000000000000000000000000000000000060000305600055'))
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 94980)

    def test_expPowerOf256Of256_12(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: expPowerOf256Of256_12.json
            sha256sum: 7ddde6fa841550682fd17bfdd5fae3238025df9241a1f9bfaaece1fcf83ef750
            Code: PUSH1 0xc
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
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=10000000)
    
        bytecode = unhexlify('600c6101000a6101000a600055600c60ff0a6101000a600155600c6101010a6101000a600255600c6101000a60ff0a600355600c60ff0a60ff0a600455600c6101010a60ff0a600555600c6101000a6101010a600655600c60ff0a6101010a600755600c6101010a6101010a600855')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 1000000

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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('600c6101000a6101000a600055600c60ff0a6101000a600155600c6101010a6101000a600255600c6101000a60ff0a600355600c60ff0a60ff0a600455600c6101010a60ff0a600555600c6101000a6101010a600655600c60ff0a6101010a600755600c6101010a6101010a600855'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x03)), 0xb0e95b83a36ce98218879ec55c33085514ff7f00000000000000000000000001)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x04)), 0xc482ab56ec19186dc48c88f30861a850b2253b1ea6dc021589e569bd47f400ff)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x05)), 0xcf45c7f9af4bbe4a83055b55b97777ad5e0a3f08b129c9ae208c5d713c0c00ff)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x06)), 0xa5cbb62a421049b0f000b68fb921f7aa6aff8100000000000000000000000001)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x07)), 0x3bde6ca66dffe1bf5d727c3edea74c7a4af43b3912e6256d37705c8f3bf40101)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x08)), 0x3f49a1e40c5213aa4ffed57eb4c1ad2d181b2aaa289e9d59c2256c43480c0101)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 863482)

    def test_expPowerOf256Of256_30(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: expPowerOf256Of256_30.json
            sha256sum: 9be1de88639c668f65e96e5d6a8580acd53611be901cdbfdd45a967d85ff4b47
            Code: PUSH1 0x1e
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
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=10000000)
    
        bytecode = unhexlify('601e6101000a6101000a600055601e60ff0a6101000a600155601e6101010a6101000a600255601e6101000a60ff0a600355601e60ff0a60ff0a600455601e6101010a60ff0a600555601e6101000a6101010a600655601e60ff0a6101010a600755601e6101010a6101010a600855')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 1000000

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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('601e6101000a6101000a600055601e60ff0a6101000a600155601e6101010a6101000a600255601e6101000a60ff0a600355601e60ff0a60ff0a600455601e6101010a60ff0a600555601e6101000a6101010a600655601e60ff0a6101010a600755601e6101010a6101010a600855'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x03)), 0x7f00000000000000000000000000000000000000000000000000000000000001)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x04)), 0xe9772778f50fa0a69cd10fa019ac56d72ac7a7d7af26c4ba28415c8f41e200ff)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x05)), 0x33f0385ef73feebdb952e5adb643dd0fa178fd9271578219ad50a73d241e00ff)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x06)), 0x8100000000000000000000000000000000000000000000000000000000000001)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x07)), 0xfd405cce8f73dffc04a6f0ff6ffc6bf7961876d09c5b4933a68f0cc623e20101)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x08)), 0xc5a8f4566fd2e96e4ce3a8b3ec0863e7b20bc3b2f3dc5261ba8a0174421e0101)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 861862)

    def test_mod1(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: mod1.json
            sha256sum: 0c9879f653ca8b0f03f685c849ecbf73657d8b7b40a1053950e30d99a05bf692
            Code: PUSH1 0x2
                  PUSH32 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
                  MOD
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('60027fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff06600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('60027fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff06600055'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0x01)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 79986)

    def test_expPowerOf256Of256_26(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: expPowerOf256Of256_26.json
            sha256sum: 9604373efccedf792396c63e83e62c70689d3d7cf3ceba25dd2fdeb37cf8308b
            Code: PUSH1 0x1a
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
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=10000000)
    
        bytecode = unhexlify('601a6101000a6101000a600055601a60ff0a6101000a600155601a6101010a6101000a600255601a6101000a60ff0a600355601a60ff0a60ff0a600455601a6101010a60ff0a600555601a6101000a6101010a600655601a60ff0a6101010a600755601a6101010a6101010a600855')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 1000000

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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('601a6101000a6101000a600055601a60ff0a6101000a600155601a6101010a6101000a600255601a6101000a60ff0a600355601a60ff0a60ff0a600455601a6101010a60ff0a600555601a6101000a6101010a600655601a60ff0a6101010a600755601a6101010a6101010a600855'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x03)), 0x085514ff7f000000000000000000000000000000000000000000000000000001)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x04)), 0x1d164db738eb6893868b361ad2803f97be35764456e82a837667a693d1e600ff)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x05)), 0x8b92c24abebf376a5aab5ff4dfd3538a03d38a10bced2aae8e1a8a85b81a00ff)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x06)), 0xf7aa6aff81000000000000000000000000000000000000000000000000000001)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x07)), 0x6931bda98c70e860a1f6a5224940f1ec7e6734cd9456c95806384f7cb7e60101)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x08)), 0x3402a9db66492dfc2a220715e76243469462f24edc56903ba1d8e96ed21a0101)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 862222)

    def test_expPowerOf256_1(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: expPowerOf256_1.json
            sha256sum: 584202e492d8a62690f8e65908748e1f05862ead2b1a3e65a02d5598ee1818d5
            Code: PUSH1 0x1
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
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('60016101000a600055600160ff0a60015560016101010a600255')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('60016101000a600055600160ff0a60015560016101010a600255'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0x0100)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x01)), 0xff)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x02)), 0x0101)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 39913)

    def test_mod2(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: mod2.json
            sha256sum: 27dc39b0ff64dfc9c5b2a79c0f75ecc32cad7ecded7d9ae1debdf1ffc4787d1d
            Code: PUSH32 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
                  PUSH1 0x0
                  MOD
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff600006600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff600006600055'))
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 94986)

    def test_expPowerOf2_4(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: expPowerOf2_4.json
            sha256sum: e3f55c2e3267c73c4125fec63c1f6b90ce6ad5d2117ce695f71eef6a6e6176df
            Code: PUSH1 0x4
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
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('600460020a600055600360020a600155600560020a600255')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('600460020a600055600360020a600155600560020a600255'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0x10)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x01)), 0x08)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x02)), 0x20)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 39913)

    def test_expPowerOf256_14(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: expPowerOf256_14.json
            sha256sum: 73f9ef5771c69fa8a9b4909d382d9c0938efdff9df3db88e2597aa71dbfbf76f
            Code: PUSH1 0xe
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
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('600e6101000a600055600e60ff0a600155600e6101010a600255')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('600e6101000a600055600e60ff0a600155600e6101010a600255'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0x010000000000000000000000000000)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x01)), 0xf25997e139ada3b331e7945af201)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x02)), 0x010e5c6ff0ddc873c2d5ea6c5b0e01)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 39913)

    def test_stop(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: stop.json
            sha256sum: 69c1ebfcd7bc87b206fa27fffa8a54a486a453cf86bfff26a0ae7270dffabb3c
            Code: STOP
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('00')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('00'))
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 100000)

    def test_sdivByZero2(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: sdivByZero2.json
            sha256sum: 3f978fa1b9337f8832324811fdd45fb9d6a5dc7034afebba9a7c909c223f78dc
            Code: PUSH1 0x1
                  PUSH1 0x0
                  PUSH32 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffcf923bdff
                  PUSH1 0x0
                  SUB
                  SDIV
                  ADD
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('600160007ffffffffffffffffffffffffffffffffffffffffffffffffffffffffcf923bdff6000030501600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('600160007ffffffffffffffffffffffffffffffffffffffffffffffffffffffffcf923bdff6000030501600055'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0x01)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 79974)

    def test_sdiv4(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: sdiv4.json
            sha256sum: 064bc920d09d94839707b16d921da2a963ae7f8d6730a48eb8d93c5baee0f7af
            Code: PUSH1 0x4
                  PUSH1 0x0
                  SUB
                  PUSH1 0x5
                  SDIV
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('6004600003600505600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('6004600003600505600055'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 79980)

    def test_expPowerOf256_7(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: expPowerOf256_7.json
            sha256sum: 61b989ba296e526bbd98acd3e0defc772990afbbaa232b82ebd8ea225b8e5a8b
            Code: PUSH1 0x7
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
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('60076101000a600055600760ff0a60015560076101010a600255')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('60076101000a600055600760ff0a60015560076101010a600255'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0x0100000000000000)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x01)), 0xf914dd22eb06ff)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x02)), 0x0107152323150701)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 39913)

    def test_add3(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: add3.json
            sha256sum: 094abae4a6da6e1506b01dd667c165c5c9c068fac674548685885f3c8fcc58cc
            Code: PUSH1 0x0
                  PUSH1 0x0
                  ADD
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('6000600001600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('6000600001600055'))
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 94988)

    def test_expPowerOf256_26(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: expPowerOf256_26.json
            sha256sum: 6ae8556c5859ce81eae1c2315b6b14d3d081bea3d4fb901a3269943ac05da3c6
            Code: PUSH1 0x1a
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
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('601a6101000a600055601a60ff0a600155601a6101010a600255')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('601a6101000a600055601a60ff0a600155601a6101010a600255'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0x010000000000000000000000000000000000000000000000000000)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x01)), 0xe73b116885641f4651a56f438fd08d61869cfa55465bd944e601)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x02)), 0x011b4f636a81778ea1c96f4cab2b998cbc26b00c572e7029451a01)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 39913)

    def test_not1(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: not1.json
            sha256sum: 13cf83235d5f2f14e56adcbbe92abdd7486d880792d166f951a4f43bd36e2898
            Code: PUSH3 0x1e240
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
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=10000000)
    
        bytecode = unhexlify('6201e2406000526000511960005260206000f3')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 1000000

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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('6201e2406000526000511960005260206000f3'))
        #check outs
        self.assertEqual(returndata, unhexlify('fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe1dbf'))
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 999967)

    def test_mul0(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: mul0.json
            sha256sum: 33b2ee01c056d260f630ce5fef98c68a54c3e4bbf64352acee459726de2a4124
            Code: PUSH1 0x3
                  PUSH1 0x2
                  MUL
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('6003600202600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('6003600202600055'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0x06)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 79986)

    def test_addmod1_overflow2(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: addmod1_overflow2.json
            sha256sum: 6d53e0173a8759687a942922b766aadd9a24b71eec1469b4fed17d2783b18a9b
            Code: PUSH1 0x5
                  PUSH1 0x0
                  PUSH1 0x1
                  PUSH1 0x0
                  SUB
                  ADDMOD
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('60056000600160000308600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 10000

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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('60056000600160000308600055'))
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 4974)

    def test_exp6(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: exp6.json
            sha256sum: 857a587c2ec9246189d9d0f9837c05d5b71f878d15635b59187d5cb63e1db3c7
            Code: PUSH2 0x101
                  PUSH1 0x1
                  EXP
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('61010160010a600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('61010160010a600055'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0x01)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 79961)

    def test_mul7(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: mul7.json
            sha256sum: eeb40b21e741cfbc21521e111beb281c4dafff4cbaaa14d53487bb9f0d8518dc
            Code: PUSH17 0x1234567890abcdef0fedcba0987654321
                  PUSH17 0x1234567890abcdef0fedcba0987654321
                  PUSH17 0x1234567890abcdef0fedcba0987654321
                  MUL
                  MUL
                  PUSH1 0x0
                  MSTORE
                  PUSH1 0x20
                  PUSH1 0x0
                  RETURN
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('7001234567890abcdef0fedcba09876543217001234567890abcdef0fedcba09876543217001234567890abcdef0fedcba0987654321020260005260206000f3')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('7001234567890abcdef0fedcba09876543217001234567890abcdef0fedcba09876543217001234567890abcdef0fedcba0987654321020260005260206000f3'))
        #check outs
        self.assertEqual(returndata, unhexlify('47d0817e4167b1eb4f9fc722b133ef9d7d9a6fb4c2c1c442d000107a5e419561'))
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 99966)

    def test_sdivByZero1(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: sdivByZero1.json
            sha256sum: 9a2207240279ed9e305737bf728c43c2b7d3bb0f40e738b88c88cad1ba8dcc63
            Code: PUSH1 0x0
                  PUSH32 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
                  PUSH1 0x0
                  SUB
                  SDIV
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('60007fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff60000305600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('60007fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff60000305600055'))
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 94980)

    def test_signextend_BitIsSetInHigherByte(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: signextend_BitIsSetInHigherByte.json
            sha256sum: 52ca3dba40a6c57773094473d20947e065012151d1739b53bdefa3745e5a07c8
            Code: PUSH3 0x12faf4
                  PUSH1 0x1
                  SIGNEXTEND
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=10000000)
    
        bytecode = unhexlify('6212faf460010b600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 1000000

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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('6212faf460010b600055'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffaf4)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 979986)

    def test_addmod2_1(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: addmod2_1.json
            sha256sum: 85890ed9d2bbf0ab3c30f1acb13082ee432641d94595b6c975097bb3a72fc840
            Code: PUSH1 0x3
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
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('60036001600660000308600360056000030614600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('60036001600660000308600360056000030614600055'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0x01)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 79954)

    def test_signextend_BitIsNotSetInHigherByte(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: signextend_BitIsNotSetInHigherByte.json
            sha256sum: a84b4f3be5bb727c6040dde6c8fcdf0267e1b1db6005ecc8234acca9e7868b5a
            Code: PUSH3 0x126af4
                  PUSH1 0x1
                  SIGNEXTEND
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=10000000)
    
        bytecode = unhexlify('62126af460010b600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 1000000

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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('62126af460010b600055'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0x6af4)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 979986)

    def test_divByNonZero0(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: divByNonZero0.json
            sha256sum: e4f4a0965d214b1ac34b98e22b3098d9574518d7e0f62916606aa70180f08b0b
            Code: PUSH1 0x2
                  PUSH1 0x5
                  DIV
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('6002600504600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('6002600504600055'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0x02)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 79986)

    def test_expPowerOf256_10(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: expPowerOf256_10.json
            sha256sum: 141e97d2625d720bc8e55bb0a9871fa8eb6120d563da1f64d8a2945be4ec018c
            Code: PUSH1 0xa
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
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('600a6101000a600055600a60ff0a600155600a6101010a600255')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('600a6101000a600055600a60ff0a600155600a6101010a600255'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0x0100000000000000000000)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x01)), 0xf62c88d104d1882cf601)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x02)), 0x010a2d78d2fcd2782d0a01)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 39913)

    def test_add0(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: add0.json
            sha256sum: 1b9624ff5644c08e974d19fb58b8b2a42b61dcf46f906b86d0794ea7ec0b2345
            Code: PUSH32 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
                  PUSH32 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
                  ADD
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff01600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff01600055'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 79988)

    def test_sdiv9(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: sdiv9.json
            sha256sum: ca75fe70e645e1c0b6b5ca6586f4f084300f5247ca8c78e0e7c57b9c3f4115a4
            Code: PUSH1 0x1
                  PUSH1 0x1
                  PUSH1 0x0
                  SUB
                  SDIV
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('6001600160000305600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('6001600160000305600055'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 79980)

    def test_expPowerOf256_11(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: expPowerOf256_11.json
            sha256sum: b432ae35edb4ed128ccf71ccae2f9d8bb48d011eb7daa694bcc3f5f22de68593
            Code: PUSH1 0xb
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
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('600b6101000a600055600b60ff0a600155600b6101010a600255')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('600b6101000a600055600b60ff0a600155600b6101010a600255'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0x010000000000000000000000)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x01)), 0xf5365c4833ccb6a4c90aff)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x02)), 0x010b37a64bcfcf4aa5370b01)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 39913)

    def test_smod2(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: smod2.json
            sha256sum: 78f2af60323f8507b529824bbe23ce7fbdf5f722392b97db8e3b1b7b348c8b05
            Code: PUSH1 0x3
                  PUSH1 0x5
                  PUSH1 0x0
                  SUB
                  SMOD
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('6003600560000307600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('6003600560000307600055'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 79980)

    def test_add4(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: add4.json
            sha256sum: ca8e6b511dceca6765685b6b80463fceadd6b15ee71c9694390828a72a884a1d
            Code: PUSH32 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
                  PUSH1 0x1
                  ADD
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff600101600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff600101600055'))
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 94988)

    def test_expPowerOf256_24(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: expPowerOf256_24.json
            sha256sum: 4aff8ff31080a4d5830af3c8497e69283cca7f730be72f1014e75246aaa435fc
            Code: PUSH1 0x18
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
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('60186101000a600055601860ff0a60015560186101010a600255')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('60186101000a600055601860ff0a60015560186101010a600255'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0x01000000000000000000000000000000000000000000000000)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x01)), 0xe90c40de00872d19573a8d23493fc3a9151e217a1913e801)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x02)), 0x01191c122a1b1745008367f9509126ae39066a3189e9141801)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 39913)

    def test_smod4(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: smod4.json
            sha256sum: 82200247a72e367fa74d3a2b2d11ebe126ee2c51861b79bc30f793010118e88c
            Code: PUSH1 0x0
                  PUSH1 0x2
                  PUSH1 0x0
                  SUB
                  SMOD
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('6000600260000307600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('6000600260000307600055'))
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 94980)

    def test_expPowerOf256Of256_19(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: expPowerOf256Of256_19.json
            sha256sum: 8e1ed67aa333e3b13521661a5a9e26d3580d9631301e1c2e9dd57b8cbf391699
            Code: PUSH1 0x13
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
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=10000000)
    
        bytecode = unhexlify('60136101000a6101000a600055601360ff0a6101000a60015560136101010a6101000a60025560136101000a60ff0a600355601360ff0a60ff0a60045560136101010a60ff0a60055560136101000a6101010a600655601360ff0a6101010a60075560136101010a6101010a600855')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 1000000

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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('60136101000a6101000a600055601360ff0a6101000a60015560136101010a6101000a60025560136101000a60ff0a600355601360ff0a60ff0a60045560136101010a60ff0a60055560136101000a6101010a600655601360ff0a6101010a60075560136101010a6101010a600855'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x03)), 0x8218879ec55c33085514ff7f0000000000000000000000000000000000000001)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x04)), 0xb795ad7ac24cfbb7435cf53bd3584f3d4b2709935635c3ceb66e761ff091feff)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x05)), 0x1f0bb7be91a0ccd0cca93d75cf03de3e6b56fe8f1c54242617665327219300ff)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x06)), 0xb0f000b68fb921f7aa6aff810000000000000000000000000000000000000001)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x07)), 0xad571756ecbff1bfdef064861e5e92c5d897a9cc380e54bdbaabd80bb793ff01)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x08)), 0xd8b5b531989e689f700dcdb43ab90e79a49dfbbb5a13dbf751df98bb34930101)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 862852)

    def test_addmod2(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: addmod2.json
            sha256sum: 1bfa788fb8650cbb35277be2e9d56d4ef9de41e10773020c16a6589b3c7479a6
            Code: PUSH1 0x3
                  PUSH1 0x1
                  PUSH1 0x6
                  PUSH1 0x0
                  SUB
                  ADDMOD
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('60036001600660000308600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('60036001600660000308600055'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0x02)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 79974)

    def test_signextend_00(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: signextend_00.json
            sha256sum: 557642b12d33eba0059e417c929fd5700c9e530b97bec89c3a5e154d6539c117
            Code: PUSH1 0x0
                  PUSH1 0x0
                  SIGNEXTEND
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=10000000)
    
        bytecode = unhexlify('600060000b600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 1000000

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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('600060000b600055'))
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 994986)

    def test_expPowerOf256_3(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: expPowerOf256_3.json
            sha256sum: 2c543fb689ceca51c0b1980c806fa2e810213ac3344812bf44b9f647ea68aa74
            Code: PUSH1 0x3
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
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('60036101000a600055600360ff0a60015560036101010a600255')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('60036101000a600055600360ff0a60015560036101010a600255'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0x01000000)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x01)), 0xfd02ff)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x02)), 0x01030301)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 39913)

    def test_addmod3_0(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: addmod3_0.json
            sha256sum: bd94167768aaa9089feaf9ea004aee1cd7728ce0beb00313054d245e41641ba0
            Code: PUSH1 0x2
                  PUSH1 0x3
                  PUSH1 0x0
                  SUB
                  PUSH1 0x1
                  PUSH1 0x4
                  ADDMOD
                  EQ
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('60026003600003600160040814600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('60026003600003600160040814600055'))
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 94968)

    def test_signextend_Overflow_dj42(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: signextend_Overflow_dj42.json
            sha256sum: 98eb87e0704d92cf48dd7c2124eb1e7c80e36955cd08cbd295d86565878a512a
            Code: PUSH1 0x5
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
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=10000000)
    
        bytecode = unhexlify('6005565b005b61800080680100000000000000010b6180011160035763badf000d601155')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 1000000

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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('6005565b005b61800080680100000000000000010b6180011160035763badf000d601155'))
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 999954)

    def test_mulmod3_0(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: mulmod3_0.json
            sha256sum: a2408325f3e9c8d5154f3c1d8d19adaad67222e2f5032350e6cee4ff7f9124c5
            Code: PUSH1 0x2
                  PUSH1 0x3
                  PUSH1 0x0
                  SUB
                  PUSH1 0x1
                  PUSH1 0x5
                  MULMOD
                  EQ
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('60026003600003600160050914600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('60026003600003600160050914600055'))
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 94968)

    def test_expPowerOf2_2(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: expPowerOf2_2.json
            sha256sum: b7e6ef69b571deadf273428a2ea22d73701409e6bfc2813874bfe7ba12687737
            Code: PUSH1 0x2
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
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('600260020a600055600160020a600155600360020a600255')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('600260020a600055600160020a600155600360020a600255'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0x04)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x01)), 0x02)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x02)), 0x08)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 39913)

    def test_arith1(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: arith1.json
            sha256sum: 89f96edaaf658fa135607f3c623751ad5fc480b5e9817580ca4725c5c523e58f
            Code: PUSH1 0x1
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
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=10000000)
    
        bytecode = unhexlify('6001600190016007026005016002900460049060016021900560150160030260059007600303600960110a60005260086000f3')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 1000000

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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('6001600190016007026005016002900460049060016021900560150160030260059007600303600960110a60005260086000f3'))
        #check outs
        self.assertEqual(returndata, unhexlify('0000000000000000'))
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 999871)

    def test_sub3(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: sub3.json
            sha256sum: 51d9d78dc7c91e221762a0d94914b0a98599d2e52fe6751aa69852ff4b7e5736
            Code: PUSH32 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
                  PUSH1 0x0
                  SUB
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff600003600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff600003600055'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0x01)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 79988)

    def test_signextendInvalidByteNumber(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: signextendInvalidByteNumber.json
            sha256sum: 7c8bbd8aaa7686a5d5644055eccba627e669859acd3f86370244ea4cfdd86bcf
            Code: PUSH3 0x126af4
                  PUSH1 0x50
                  SIGNEXTEND
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=10000000)
    
        bytecode = unhexlify('62126af460500b600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 1000000

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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('62126af460500b600055'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0x126af4)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 979986)

    def test_mulmod1(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: mulmod1.json
            sha256sum: 0627eddadc1ab556e263b67f4cf1a33102073c638f800756cfec5eefd47161c7
            Code: PUSH1 0x3
                  PUSH1 0x2
                  PUSH1 0x0
                  SUB
                  PUSH1 0x1
                  PUSH1 0x0
                  SUB
                  MULMOD
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('60036002600003600160000309600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('60036002600003600160000309600055'))
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 94968)

    def test_mulmod1_overflow4(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: mulmod1_overflow4.json
            sha256sum: a11a3a3f24b290e9d035fde4aa7967e8a4018382a3c72799e6105d188134f573
            Code: PUSH1 0x5
                  PUSH1 0x2
                  PUSH32 0x8000000000000000000000000000000000000000000000000000000000000001
                  MULMOD
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('600560027f800000000000000000000000000000000000000000000000000000000000000109600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 1000000

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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('600560027f800000000000000000000000000000000000000000000000000000000000000109600055'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0x03)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 979980)

    def test_expPowerOf256Of256_9(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: expPowerOf256Of256_9.json
            sha256sum: 773dd1eb4eed06df60aea02095374c3442a0b521cb90605e85a8a6bfbce5ef2b
            Code: PUSH1 0x9
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
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=10000000)
    
        bytecode = unhexlify('60096101000a6101000a600055600960ff0a6101000a60015560096101010a6101000a60025560096101000a60ff0a600355600960ff0a60ff0a60045560096101010a60ff0a60055560096101000a6101010a600655600960ff0a6101010a60075560096101010a6101010a600855')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 1000000

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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('60096101000a6101000a600055600960ff0a6101000a60015560096101010a6101000a60025560096101000a60ff0a600355600960ff0a60ff0a60045560096101010a60ff0a60055560096101000a6101010a600655600960ff0a6101010a60075560096101010a6101010a600855'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x03)), 0x53017d8eb210db2c8cd4a299079ec55c33085514ff7f00000000000000000001)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x04)), 0x48be09b6c6ae2aa660f1972125cecbb1038b5d236ecf766ba786e2c4e887feff)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x05)), 0x2e350d847ba73dc2099f83f532951c47269d9fd7e411b50bae00a9581f8900ff)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x06)), 0x013ab9e1f0df89a184b4d07080b68fb921f7aa6aff8100000000000000000001)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x07)), 0xf387ed41c1050f9da667f429a3e8fb30b61a55ede97d7b8acd797a03cd89ff01)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x08)), 0x525696c22bb3ce00fd2e3f6bbb9b4ea1046a5e31fcff2fedf8f8c74d28890101)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 863752)

    def test_exp3(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: exp3.json
            sha256sum: 30aff2bd2353be208e4964a24a76d95d6c5e8d4c272189219c821ab7f4aae95d
            Code: PUSH4 0x7fffffff
                  PUSH1 0x0
                  EXP
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('637fffffff60000a600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('637fffffff60000a600055'))
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 94941)

    def test_sub2(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: sub2.json
            sha256sum: 6df63508965f32e5b145e711c7a7d5a0226182745ad7ced9596d22e869d4ce26
            Code: PUSH1 0x17
                  PUSH1 0x0
                  SUB
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('6017600003600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('6017600003600055'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe9)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 79988)

    def test_signextend_bigBytePlus1(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: signextend_bigBytePlus1.json
            sha256sum: c0e78b1d5a7d5a0aa6d620252bc5d3e2f90da0570222ed61a1f7ec33a2e9b0a3
            Code: PUSH7 0xf0000000000001
                  PUSH2 0xffff
                  SIGNEXTEND
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=10000000)
    
        bytecode = unhexlify('66f000000000000161ffff0b600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 1000000

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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('66f000000000000161ffff0b600055'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0xf0000000000001)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 979986)

    def test_expPowerOf256_15(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: expPowerOf256_15.json
            sha256sum: 324a9bdb004fc56a3a395a7c249e5a8dacb87933c42706853dce0870c59dd1f9
            Code: PUSH1 0xf
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
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('600f6101000a600055600f60ff0a600155600f6101010a600255')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('600f6101000a600055600f60ff0a600155600f6101010a600255'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0x01000000000000000000000000000000)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x01)), 0xf1673e495873f60f7eb5acc6970eff)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x02)), 0x010f6acc60cea63c3698c056c7690f01)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 39913)

    def test_addmod1_overflow4(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: addmod1_overflow4.json
            sha256sum: fe6cf50ca2f047306b0651dc05dad77abfd1020d720c8f7f9a3ce880e7c1a883
            Code: PUSH1 0x5
                  PUSH1 0x2
                  PUSH1 0x1
                  PUSH1 0x0
                  SUB
                  ADDMOD
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('60056002600160000308600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 1000000

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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('60056002600160000308600055'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0x02)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 979974)

    def test_sub4(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: sub4.json
            sha256sum: 7aa553398de51c541b626d1f247ca57e6fe0037f64ef1e25f8811eabd8c32333
            Code: PUSH1 0x0
                  PUSH32 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
                  SUB
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('60007fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff03600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('60007fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff03600055'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 79988)

    def test_expPowerOf256_4(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: expPowerOf256_4.json
            sha256sum: 2c69a6e43ce8c44ae607fd6eb3b2fc3bda3955f616443834561d2591e66a2b5c
            Code: PUSH1 0x4
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
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('60046101000a600055600460ff0a60015560046101010a600255')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('60046101000a600055600460ff0a60015560046101010a600255'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0x0100000000)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x01)), 0xfc05fc01)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x02)), 0x0104060401)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 39913)

    def test_expPowerOf256_30(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: expPowerOf256_30.json
            sha256sum: 40b900a85b4a54fda4efc8e6bcdbf7ba6b7535de4223a3479188966314336500
            Code: PUSH1 0x1e
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
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('601e6101000a600055601e60ff0a600155601e6101010a600255')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('601e6101000a600055601e60ff0a600155601e6101010a600255'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0x01000000000000000000000000000000000000000000000000000000000000)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x01)), 0xe3a38ce946b71e74e8ebc966d90f0b139e66b560e1f5b542c0fd25b2e201)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x02)), 0x011fc34942d8d9831a0811d8412aecf1e1f58031ffbc16699c151cddb31e01)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 39913)

    def test_mul4(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: mul4.json
            sha256sum: 2af8c375f77e6c86727181d0e3f29f8dbaf405887b13334db8a96f03b44d6f09
            Code: PUSH32 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
                  PUSH32 0x8000000000000000000000000000000000000000000000000000000000000000
                  MUL
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7f800000000000000000000000000000000000000000000000000000000000000002600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7f800000000000000000000000000000000000000000000000000000000000000002600055'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0x8000000000000000000000000000000000000000000000000000000000000000)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 79986)

    def test_sdiv8(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: sdiv8.json
            sha256sum: ae920601baa46dd4e819c59770df6a4df3283f34525ca348cfbefed8fedf2b83
            Code: PUSH1 0x1
                  PUSH1 0x0
                  SUB
                  PUSH1 0x1
                  PUSH1 0x0
                  SUB
                  SDIV
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('6001600003600160000305600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('6001600003600160000305600055'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0x01)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 79974)

    def test_addmodDivByZero2(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: addmodDivByZero2.json
            sha256sum: 8ff606d5cf2b15305c314d3aac201a020656517db4b5b8a5730996bf2dc1b161
            Code: PUSH1 0x0
                  PUSH1 0x0
                  PUSH1 0x1
                  ADDMOD
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('60006000600108600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('60006000600108600055'))
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 94980)

    def test_expPowerOf256Of256_8(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: expPowerOf256Of256_8.json
            sha256sum: 670bc5532f9085f0b0ba382e693a5b57ce1674ec3c25cabef57cb97fd5b41962
            Code: PUSH1 0x8
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
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=100000000)
    
        bytecode = unhexlify('60086101000a6101000a600055600860ff0a6101000a60015560086101010a6101000a60025560086101000a60ff0a600355600860ff0a60ff0a60045560086101010a60ff0a60055560086101000a6101010a600655600860ff0a6101010a60075560086101010a6101010a600855')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 10000000

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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('60086101000a6101000a600055600860ff0a6101000a60015560086101010a6101000a60025560086101000a60ff0a600355600860ff0a60ff0a60045560086101010a60ff0a60055560086101000a6101010a600655600860ff0a6101010a60075560086101010a6101010a600855'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x03)), 0x230041a0e7602d6e459609ed39081ec55c33085514ff7f000000000000000001)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x04)), 0xc407d8a413ef9079ead457ed686a05ac81039c0cae0a7f6afd01e8461ff800ff)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x05)), 0x67a397e0692385e4cd83853aabce220a94d449e885fa867e96d3ef5e180800ff)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x06)), 0x70add926e753655d6d0ebe9c0f81368fb921f7aa6aff81000000000000000001)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x07)), 0x0bdce80b8378e43f13d454b9d0a4c83cf311b8eaa45d5122cfd544a217f80101)
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x08)), 0x629c25790e1488998877a9ecdf0fb69637e77d8a4bdc1b46270093ba20080101)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 9863842)

if __name__ == '__main__':
    unittest.main()
