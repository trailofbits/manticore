
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

class EVMTest_vmArithmeticTest(unittest.TestCase):
    _multiprocess_can_split_ = True
    maxDiff=None 


    def test_addmodDivByZero1(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest/addmodDivByZero1.json
            sha256sum: d74a217015c5c549f6df05e8cbfad950327204f7c1f5c9f389e9e09d0aeeddc8
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
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('60006001600008600055'))
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 94980)

    def test_mulmod2_0(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest/mulmod2_0.json
            sha256sum: d568c5e880beaf0af42cf9f02325b223573a7370cc5335ba7c96984ff586e2f7
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
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('60036001600560000309600360056000030714600055'))
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 94954)

    def test_expPowerOf2_64(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest/expPowerOf2_64.json
            sha256sum: 98d78866c1ea1c477e2c7c22f92c2497a823ecf8947f0a2a073ea35608a447e9
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
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('604060020a600055603f60020a600155604160020a600255'))
        #check storage
        self.assertEqual(world.get_storage_data(account_address, 0x00), 0x010000000000000000)
        self.assertEqual(world.get_storage_data(account_address, 0x01), 0x8000000000000000)
        self.assertEqual(world.get_storage_data(account_address, 0x02), 0x020000000000000000)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 39913)

    def test_sdiv5(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest/sdiv5.json
            sha256sum: 1d5770423cb41401b9d81279c8707d877712e62cfc763b7f6fa5e80973895e09
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
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('60016000037f800000000000000000000000000000000000000000000000000000000000000060000305600055'))
        #check storage
        self.assertEqual(world.get_storage_data(account_address, 0x00), 0x8000000000000000000000000000000000000000000000000000000000000000)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 79974)

    def test_expPowerOf256Of256_0(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest/expPowerOf256Of256_0.json
            sha256sum: aaf201b6fb29f2a6532a93084c812fe91e47d3a1b3f9823c39203e6481c9547a
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
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 1000000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('60006101000a6101000a600055600060ff0a6101000a60015560006101010a6101000a60025560006101000a60ff0a600355600060ff0a60ff0a60045560006101010a60ff0a60055560006101000a6101010a600655600060ff0a6101010a60075560006101010a6101010a600855'))
        #check storage
        self.assertEqual(world.get_storage_data(account_address, 0x00), 0x0100)
        self.assertEqual(world.get_storage_data(account_address, 0x01), 0x0100)
        self.assertEqual(world.get_storage_data(account_address, 0x02), 0x0100)
        self.assertEqual(world.get_storage_data(account_address, 0x03), 0xff)
        self.assertEqual(world.get_storage_data(account_address, 0x04), 0xff)
        self.assertEqual(world.get_storage_data(account_address, 0x05), 0xff)
        self.assertEqual(world.get_storage_data(account_address, 0x06), 0x0101)
        self.assertEqual(world.get_storage_data(account_address, 0x07), 0x0101)
        self.assertEqual(world.get_storage_data(account_address, 0x08), 0x0101)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 819622)

    def test_sdiv0(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest/sdiv0.json
            sha256sum: d39c4cd369902b61108961b95c639f1efbeca8065147b2ce106978deb1df4b82
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
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff60000305600055'))
        #check storage
        self.assertEqual(world.get_storage_data(account_address, 0x00), 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 79980)

    def test_expPowerOf2_256(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest/expPowerOf2_256.json
            sha256sum: 4b2dc6aa2f27c0e76677800bfacd210cb8600750eb22fb898a25270a9119dd0d
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
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('61010060020a60005560ff60020a60015561010160020a600255'))
        #check storage
        self.assertEqual(world.get_storage_data(account_address, 0x01), 0x8000000000000000000000000000000000000000000000000000000000000000)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 69893)

    def test_expPowerOf256_12(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest/expPowerOf256_12.json
            sha256sum: 22bbdcc937593b86f4d2a175a5e2981d968cb2967aebb37c514488a14e936503
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
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('600c6101000a600055600c60ff0a600155600c6101010a600255'))
        #check storage
        self.assertEqual(world.get_storage_data(account_address, 0x00), 0x01000000000000000000000000)
        self.assertEqual(world.get_storage_data(account_address, 0x01), 0xf44125ebeb98e9ee2441f401)
        self.assertEqual(world.get_storage_data(account_address, 0x02), 0x010c42ddf21b9f19efdc420c01)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 39913)

    def test_expPowerOf256_9(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest/expPowerOf256_9.json
            sha256sum: 10d52dcd705f6eedb88c52f663d5795d13412556b7208d9e13efe6dc736ba325
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
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('60096101000a600055600960ff0a60015560096101010a600255'))
        #check storage
        self.assertEqual(world.get_storage_data(account_address, 0x00), 0x01000000000000000000)
        self.assertEqual(world.get_storage_data(account_address, 0x01), 0xf723ac7d8253dc08ff)
        self.assertEqual(world.get_storage_data(account_address, 0x02), 0x010924547e7e54240901)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 39913)

    def test_expPowerOf2_8(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest/expPowerOf2_8.json
            sha256sum: a540a4e8b573b1d1793099c8ddb4a12e3ec5689c1d331ad58963323f78b5cdc0
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
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('600860020a600055600760020a600155600960020a600255'))
        #check storage
        self.assertEqual(world.get_storage_data(account_address, 0x00), 0x0100)
        self.assertEqual(world.get_storage_data(account_address, 0x01), 0x80)
        self.assertEqual(world.get_storage_data(account_address, 0x02), 0x0200)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 39913)

    def test_expPowerOf256_28(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest/expPowerOf256_28.json
            sha256sum: 832d1166571800fd900dc4e14d42460d0bec2fd55214d74113330c20477aeca4
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
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('601c6101000a600055601c60ff0a600155601c6101010a600255'))
        #check storage
        self.assertEqual(world.get_storage_data(account_address, 0x00), 0x0100000000000000000000000000000000000000000000000000000000)
        self.assertEqual(world.get_storage_data(account_address, 0x01), 0xe56d8280c5c1dc6be448760a77f47c1750f146fd962467ee3579e401)
        self.assertEqual(world.get_storage_data(account_address, 0x02), 0x011d871d80b9e4ff369ba3f4b3ce9beb6f2bb9931fe9243807cd7a1c01)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 39913)

    def test_expPowerOf256Of256_32(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest/expPowerOf256Of256_32.json
            sha256sum: c182dc46bb35c07e60e5a2c055a520e5b70358c08bef850e475a4f91d96836e4
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
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 1000000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('60206101000a6101000a600055602060ff0a6101000a60015560206101010a6101000a60025560206101000a60ff0a600355602060ff0a60ff0a60045560206101010a60ff0a60055560206101000a6101010a600655602060ff0a6101010a60075560206101010a6101010a600855'))
        #check storage
        self.assertEqual(world.get_storage_data(account_address, 0x00), 0x01)
        self.assertEqual(world.get_storage_data(account_address, 0x03), 0x01)
        self.assertEqual(world.get_storage_data(account_address, 0x04), 0xb8247842bb5ce75c08d0c251669ed5870fa24a22952e5db3a7c66c59ffe000ff)
        self.assertEqual(world.get_storage_data(account_address, 0x05), 0xee526e5a06f2a990b2bf6c951e5feabf0e07ee16877296e1be872db9e02000ff)
        self.assertEqual(world.get_storage_data(account_address, 0x06), 0x01)
        self.assertEqual(world.get_storage_data(account_address, 0x07), 0xeda7d024b6de40a9d3b966e71f10a4667edc5b71cab07aeabcac6249dfe00101)
        self.assertEqual(world.get_storage_data(account_address, 0x08), 0x512ecfaeeb11205f0833e1054dcb1300488e0954be5af77a49e143aa00200101)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 847702)

    def test_expPowerOf256_13(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest/expPowerOf256_13.json
            sha256sum: a4c136c2a324a8e1d73e6b09656c6797445b6dd1920a9da8b0657367a1ebfc0f
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
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('600d6101000a600055600d60ff0a600155600d6101010a600255'))
        #check storage
        self.assertEqual(world.get_storage_data(account_address, 0x00), 0x0100000000000000000000000000)
        self.assertEqual(world.get_storage_data(account_address, 0x01), 0xf34ce4c5ffad5104361db20cff)
        self.assertEqual(world.get_storage_data(account_address, 0x02), 0x010d4f20d00dbab909cc1e4e0d01)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 39913)

    def test_expPowerOf256_20(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest/expPowerOf256_20.json
            sha256sum: 47586d6cdc3bc4f3409d585606a9a271546d1e3e74bf4c78c7a67d5ffbd1c197
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
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('60146101000a600055601460ff0a60015560146101010a600255'))
        #check storage
        self.assertEqual(world.get_storage_data(account_address, 0x00), 0x010000000000000000000000000000000000000000)
        self.assertEqual(world.get_storage_data(account_address, 0x01), 0xecb99eb1063b1984b725d2e3c72b82e88cbdec01)
        self.assertEqual(world.get_storage_data(account_address, 0x02), 0x0114c2872a2898bea4ec46054167a4a2f174be1401)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 39913)

    def test_divByZero(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest/divByZero.json
            sha256sum: 1a9cb7d4ba10631c903bd1589d6a229f4ca5158eee7d95596ca58b4434d2044e
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
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('6000600204600055'))
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 94986)

    def test_expPowerOf256Of256_33(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest/expPowerOf256Of256_33.json
            sha256sum: 8d279e113235bd8a8df5716c18db5439ce7a502c0ccd966aa16249cccc526eae
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
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 1000000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('60216101000a6101000a600055602160ff0a6101000a60015560216101010a6101000a60025560216101000a60ff0a600355602160ff0a60ff0a60045560216101010a60ff0a60055560216101000a6101010a600655602160ff0a6101010a60075560216101010a6101010a600855'))
        #check storage
        self.assertEqual(world.get_storage_data(account_address, 0x00), 0x01)
        self.assertEqual(world.get_storage_data(account_address, 0x03), 0x01)
        self.assertEqual(world.get_storage_data(account_address, 0x04), 0x8dcb65b5494eba78cd6756a6f9851f6e26d0f2bb9ecd7e9abd7e9b11209ffeff)
        self.assertEqual(world.get_storage_data(account_address, 0x05), 0x6694bb31b20cd625f3756897dae6d738f2e64467b5b6f10fa3e07763ffa100ff)
        self.assertEqual(world.get_storage_data(account_address, 0x06), 0x01)
        self.assertEqual(world.get_storage_data(account_address, 0x07), 0xe678999aeffd1f1f45081f64de7f80ab083dd7df04721ed64ee04c03bda1ff01)
        self.assertEqual(world.get_storage_data(account_address, 0x08), 0x39b68fb9898dd7568abd178397251ce8226a25c1d305a4e79573333520a10101)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 847702)

    def test_expPowerOf256_22(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest/expPowerOf256_22.json
            sha256sum: 713d3c587b99f1c6e041cbc14a70de887b7ad73fb433fe1de6f9cca19badebd6
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
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('60166101000a600055601660ff0a60015560166101010a600255'))
        #check storage
        self.assertEqual(world.get_storage_data(account_address, 0x00), 0x0100000000000000000000000000000000000000000000)
        self.assertEqual(world.get_storage_data(account_address, 0x01), 0xeae1182d42dfa98cc73c3e63d280f30e3e8cfce6ea01)
        self.assertEqual(world.get_storage_data(account_address, 0x02), 0x0116ed20fb041418baf4c37d91efb553dbfa9904e71601)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 39913)

    def test_signextend_BigByte_0(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest/signextend_BigByte_0.json
            sha256sum: 0c22971dddcacaf8c749c6664a98f9462014c4a8ef8e083bb6199169f479e71b
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
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 1000000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('60007fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0b600055'))
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 994986)

    def test_mul1(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest/mul1.json
            sha256sum: 42365a2a9e2993f6c46e0e4a7fee6ca500a24a2d255c519c19f929c9627377da
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
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff02600055'))
        #check storage
        self.assertEqual(world.get_storage_data(account_address, 0x00), 0x01)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 79986)

    def test_exp7(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest/exp7.json
            sha256sum: 9245e1406739baf54abdbd658a9b296f2cf9b68646652a19f94f547890e2cfd9
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
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('61010160020a600055'))
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 94961)

    def test_expPowerOf256Of256_29(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest/expPowerOf256Of256_29.json
            sha256sum: 093edab19d560c1ec26167e5f0a9d48bdb710db8ff76153774bafe0572b991cd
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
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 1000000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('601d6101000a6101000a600055601d60ff0a6101000a600155601d6101010a6101000a600255601d6101000a60ff0a600355601d60ff0a60ff0a600455601d6101010a60ff0a600555601d6101000a6101010a600655601d60ff0a6101010a600755601d6101010a6101010a600855'))
        #check storage
        self.assertEqual(world.get_storage_data(account_address, 0x03), 0xff7f000000000000000000000000000000000000000000000000000000000001)
        self.assertEqual(world.get_storage_data(account_address, 0x04), 0x41e065d46e0349cfe624c4e8a2034aea1f7edfff80e511cd8067d488949bfeff)
        self.assertEqual(world.get_storage_data(account_address, 0x05), 0xa84162ca6675a22c4c79dfc4ea15f760db5a04dbf04246764199b668879d00ff)
        self.assertEqual(world.get_storage_data(account_address, 0x06), 0xff81000000000000000000000000000000000000000000000000000000000001)
        self.assertEqual(world.get_storage_data(account_address, 0x07), 0x1226984faa6b05ebdbd45d8477fa4fd5b55bfd5061de03c319282b153d9dff01)
        self.assertEqual(world.get_storage_data(account_address, 0x08), 0x5cc9e6b0b749fd94541ad00364bdec2fca7816981ca3e38f485decc7a49d0101)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 861952)

    def test_expPowerOf256_33(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest/expPowerOf256_33.json
            sha256sum: 78ca3eeaa9f8fd60d54f34c9c8b6b565676025f60948cf7df3be336051949cfe
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
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('60216101000a600055602160ff0a60015560216101010a600255'))
        #check storage
        self.assertEqual(world.get_storage_data(account_address, 0x01), 0xfb4c498e11e3f82e714be514ef024675bb48d678bd192222cd2e783d4df020ff)
        self.assertEqual(world.get_storage_data(account_address, 0x02), 0x25f3884075dd08b8fb400789097aa95df8750bd17be0d83c9a0fb7ed52102101)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 54913)

    def test_addmod3(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest/addmod3.json
            sha256sum: 76782ea2142b1b24f5be35246de88ed1af6f28de1e0d1ace42a0fc0deb7a539c
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
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('60036000036001600408600055'))
        #check storage
        self.assertEqual(world.get_storage_data(account_address, 0x00), 0x05)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 79974)

    def test_sdivByZero0(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest/sdivByZero0.json
            sha256sum: d23d2206beceac565904c33ccb782d4c45b879708d62788151cda450c87ccd54
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
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('6000600003600360000305600055'))
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 94974)

    def test_mod4(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest/mod4.json
            sha256sum: abfc01200e89a302826f7972391008778b7482bf5cc046200474087b4e5041b6
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
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('6003600260000306600055'))
        #check storage
        self.assertEqual(world.get_storage_data(account_address, 0x00), 0x02)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 79980)

    def test_expPowerOf256Of256_6(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest/expPowerOf256Of256_6.json
            sha256sum: 5cf8d9cc80003e1db4517b36b9bfd9e412f58d224201cf3e090be0e274838e08
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
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 1000000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('60066101000a6101000a600055600660ff0a6101000a60015560066101010a6101000a60025560066101000a60ff0a600355600660ff0a60ff0a60045560066101010a60ff0a60055560066101000a6101010a600655600660ff0a6101010a60075560066101010a6101010a600855'))
        #check storage
        self.assertEqual(world.get_storage_data(account_address, 0x03), 0x1948059de1def03c4ec35fc22c2bb8f2bf45dc33085514ff7f00000000000001)
        self.assertEqual(world.get_storage_data(account_address, 0x04), 0x41f818a8e24eb6d7bb7b193b4f2b5fdcf4bd0d453f2ac3499d8830d391fa00ff)
        self.assertEqual(world.get_storage_data(account_address, 0x05), 0xede6fe4a943dfb5d967a2b85d6728759d40d2ef0ae4bc28bbb1867f98c0600ff)
        self.assertEqual(world.get_storage_data(account_address, 0x06), 0x083c936cbaad5de592badc2e142fe4ebd6103921f7aa6aff8100000000000001)
        self.assertEqual(world.get_storage_data(account_address, 0x07), 0x57385019fe4e0939ca3f35c37cadfaf52fba5b1cdfb02def3866e8068bfa0101)
        self.assertEqual(world.get_storage_data(account_address, 0x08), 0x810ac878bd98428f6be8c6426ba9f9da09e3e33bf4fe10bfa3f8b12c92060101)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 864022)

    def test_expXY(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest/expXY.json
            sha256sum: 36065cb855ef7957e1df71e2bbd690d561f171745b7c20e3601badf33cdbec8a
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
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = unhexlify('0000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000100000000000f')
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('6000356000556020356001556001546000540a600255'))
        #check storage
        self.assertEqual(world.get_storage_data(account_address, 0x00), 0x02)
        self.assertEqual(world.get_storage_data(account_address, 0x01), 0x0100000000000f)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 54793)

    def test_mulmod2_1(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest/mulmod2_1.json
            sha256sum: 2844303991e2c79b5ebd00b219a6a8c73f7bdfa2fcbe575000d7512b10d73d72
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
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('60036001600560000309600360056000030614600055'))
        #check storage
        self.assertEqual(world.get_storage_data(account_address, 0x00), 0x01)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 79954)

    def test_expPowerOf256Of256_3(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest/expPowerOf256Of256_3.json
            sha256sum: b3af73512cce1c54c4f9a7ed5655e21352a3452361df1bd414e4c7c7c9216a58
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
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 1000000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('60036101000a6101000a600055600360ff0a6101000a60015560036101010a6101000a60025560036101000a60ff0a600355600360ff0a60ff0a60045560036101010a60ff0a60055560036101000a6101010a600655600360ff0a6101010a60075560036101010a6101010a600855'))
        #check storage
        self.assertEqual(world.get_storage_data(account_address, 0x03), 0x109a00e1370d2d2922bf892e85becb54297354b2e5c75388d514ff7f00000001)
        self.assertEqual(world.get_storage_data(account_address, 0x04), 0x54a792f15e9aba7e4ad9e716bc169eea3a6e2e9c49bf9b335874613c8081feff)
        self.assertEqual(world.get_storage_data(account_address, 0x05), 0x5d24a14d8e5e039372cd0f6a0f31e9ed6b75adba9f16b1c5b3edd5ba818300ff)
        self.assertEqual(world.get_storage_data(account_address, 0x06), 0x298e2f316b4ccded5ebf515998d9ec20df69404b04a441782a6aff8100000001)
        self.assertEqual(world.get_storage_data(account_address, 0x07), 0x4335694e98f372183c62a2339fa4ad161e9b4c42240bdc9452abffd07783ff01)
        self.assertEqual(world.get_storage_data(account_address, 0x08), 0xf0f0820797315acd063056bba76f6a9c3e281cdb5197a233967ca94684830101)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 864292)

    def test_expPowerOf256Of256_10(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest/expPowerOf256Of256_10.json
            sha256sum: c20d0eb40353426098df4cc80126a7c21aa936427830409ad6a93396d08cb022
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
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 1000000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('600a6101000a6101000a600055600a60ff0a6101000a600155600a6101010a6101000a600255600a6101000a60ff0a600355600a60ff0a60ff0a600455600a6101010a60ff0a600555600a6101000a6101010a600655600a60ff0a6101010a600755600a6101010a6101010a600855'))
        #check storage
        self.assertEqual(world.get_storage_data(account_address, 0x03), 0xfe0f60957dc223578a0298879ec55c33085514ff7f0000000000000000000001)
        self.assertEqual(world.get_storage_data(account_address, 0x04), 0xc1ea45f348b5d351c4d8fe5c77da979cadc33d866acc42e981278896b1f600ff)
        self.assertEqual(world.get_storage_data(account_address, 0x05), 0x56ddb29bca94fb986ac0a40188b3b53f3216b3559bd8324a77ea8bd8a80a00ff)
        self.assertEqual(world.get_storage_data(account_address, 0x06), 0x2d49ff6b0bbe177ae9317000b68fb921f7aa6aff810000000000000000000001)
        self.assertEqual(world.get_storage_data(account_address, 0x07), 0x185fa9eab94cfe3016b69657e83b23fd24cc6960218254231c3db627a7f60101)
        self.assertEqual(world.get_storage_data(account_address, 0x08), 0xa7a0223829f26d6c635368034320563df4aa5eb62efc87a42bb35f69b20a0101)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 863662)

    def test_expPowerOf256Of256_17(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest/expPowerOf256Of256_17.json
            sha256sum: 72f41dfd2636aed5b48e70020056642323afe27643f6a130402325a3de1b8755
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
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 1000000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('60116101000a6101000a600055601160ff0a6101000a60015560116101010a6101000a60025560116101000a60ff0a600355601160ff0a60ff0a60045560116101010a60ff0a60055560116101000a6101010a600655601160ff0a6101010a60075560116101010a6101010a600855'))
        #check storage
        self.assertEqual(world.get_storage_data(account_address, 0x03), 0xec698218879ec55c33085514ff7f000000000000000000000000000000000001)
        self.assertEqual(world.get_storage_data(account_address, 0x04), 0x722ad218eb1995a2d257c4c06d8de993c203cfc8e3512df7d633e17e908ffeff)
        self.assertEqual(world.get_storage_data(account_address, 0x05), 0x8ac9b5ec08d74612cb29f941481d274b51721af2296207c0da8d24667f9100ff)
        self.assertEqual(world.get_storage_data(account_address, 0x06), 0x8fc9b0f000b68fb921f7aa6aff81000000000000000000000000000000000001)
        self.assertEqual(world.get_storage_data(account_address, 0x07), 0x81d5ff63680841482299f3eab616446dcd336f537c0c565aa4112ab95d91ff01)
        self.assertEqual(world.get_storage_data(account_address, 0x08), 0x9c6ca90dac4e97dea02ac969e8649ee9e6232e0c3f4797411151cb8f90910101)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 863032)

    def test_expPowerOf256Of256_27(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest/expPowerOf256Of256_27.json
            sha256sum: d79de8ebea93f3d33f70869eb85a750bb91f6b68f069aad2c3b7a4fba5f17eae
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
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 1000000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('601b6101000a6101000a600055601b60ff0a6101000a600155601b6101010a6101000a600255601b6101000a60ff0a600355601b60ff0a60ff0a600455601b6101010a60ff0a600555601b6101000a6101010a600655601b60ff0a6101010a600755601b6101010a6101010a600855'))
        #check storage
        self.assertEqual(world.get_storage_data(account_address, 0x03), 0x5514ff7f00000000000000000000000000000000000000000000000000000001)
        self.assertEqual(world.get_storage_data(account_address, 0x04), 0x178918ffbcb401d4efd2f7dfb4d01a897172267f0f491121ac52dd614899feff)
        self.assertEqual(world.get_storage_data(account_address, 0x05), 0x38ecff71480ca0b422f2ed6f780d5fead2ae234a49104b10a86f7f0dd19b00ff)
        self.assertEqual(world.get_storage_data(account_address, 0x06), 0xaa6aff8100000000000000000000000000000000000000000000000000000001)
        self.assertEqual(world.get_storage_data(account_address, 0x07), 0xd02811cb5dc1d80567e810532b235b7672f5c78cd6e89bb511d5e2d8f79bff01)
        self.assertEqual(world.get_storage_data(account_address, 0x08), 0x1b4e6404f474c18055d30bb8987672f59e97980d6f9de1764c0fbec5ec9b0101)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 862132)

    def test_expPowerOf256_21(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest/expPowerOf256_21.json
            sha256sum: 85694e3edf0c5c4f8bb283d1929df3a4ecdb8bb7d33a72fd54ce5f18536093cc
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
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('60156101000a600055601560ff0a60015560156101010a600255'))
        #check storage
        self.assertEqual(world.get_storage_data(account_address, 0x00), 0x01000000000000000000000000000000000000000000)
        self.assertEqual(world.get_storage_data(account_address, 0x01), 0xebcce5125534de6b326ead10e3645765a4312e14ff)
        self.assertEqual(world.get_storage_data(account_address, 0x02), 0x0115d749b152c1576391324b46a90c47946632d21501)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 39913)

    def test_addmodDivByZero3(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest/addmodDivByZero3.json
            sha256sum: a5054faec34a8f141a34764722ef41a90eda4fa838de2c5faf7d46cffb55310b
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
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('60016000600060000803600055'))
        #check storage
        self.assertEqual(world.get_storage_data(account_address, 0x00), 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 79974)

    def test_expPowerOf256_16(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest/expPowerOf256_16.json
            sha256sum: 80681256ec8c75eac1fe7ca9a66be9a94279a7292d4aa27041a3670d3c6ddb28
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
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('60106101000a600055601060ff0a60015560106101010a600255'))
        #check storage
        self.assertEqual(world.get_storage_data(account_address, 0x00), 0x0100000000000000000000000000000000)
        self.assertEqual(world.get_storage_data(account_address, 0x01), 0xf075d70b0f1b82196f36f719d077f001)
        self.assertEqual(world.get_storage_data(account_address, 0x02), 0x01107a372d2f74e272cf59171e30781001)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 39913)

    def test_exp1(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest/exp1.json
            sha256sum: defdc509816e0880d0b42289987c17714957f6f1cc21d770d85dc617491d6bed
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
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0a600055'))
        #check storage
        self.assertEqual(world.get_storage_data(account_address, 0x00), 0x01)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 79661)

    def test_sdiv_dejavu(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest/sdiv_dejavu.json
            sha256sum: 016b49648abb249df1fca33709099268f5ca7766d9403df4666977512c6cca3a
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
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x1
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 10000000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('600560096000030580600055'))
        #check storage
        self.assertEqual(world.get_storage_data(account_address, 0x00), 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 9979977)

    def test_addmodBigIntCast(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest/addmodBigIntCast.json
            sha256sum: 864fa92a671eba1f133d95b6cfc57e70d8d12bbc8440a7a782cd134bdac8b946
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
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('600560017fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff08600055'))
        #check storage
        self.assertEqual(world.get_storage_data(account_address, 0x00), 0x01)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 79980)

    def test_smod1(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest/smod1.json
            sha256sum: 9c0d9b64aab23eb814bd045f6665b57260613a8b16a14d91ef5822b4c68b8549
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
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('6003600003600507600055'))
        #check storage
        self.assertEqual(world.get_storage_data(account_address, 0x00), 0x02)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 79980)

    def test_addmod1_overflowDiff(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest/addmod1_overflowDiff.json
            sha256sum: 29a47586a6f58a18aa102ebc6773b8531bb18671ec5975724e83ab8957e03c5f
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
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 1000000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('60056002600003600160000308600055'))
        #check storage
        self.assertEqual(world.get_storage_data(account_address, 0x00), 0x04)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 979968)

    def test_exp2(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest/exp2.json
            sha256sum: dec405532cd04c5cb4dee7441a2d477f3652f881d8881439a0352e709b31f27d
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
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('637fffffff637fffffff0a600055'))
        #check storage
        self.assertEqual(world.get_storage_data(account_address, 0x00), 0xbc8cccccccc888888880000000aaaaaab00000000fffffffffffffff7fffffff)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 79941)

    def test_exp0(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest/exp0.json
            sha256sum: b15e9a5c9bec6c15f07ce885a55cd91d816c3c75d8463a75cec61029d7f85473
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
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('600260020a600055'))
        #check storage
        self.assertEqual(world.get_storage_data(account_address, 0x00), 0x04)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 79971)

    def test_divByNonZero1(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest/divByNonZero1.json
            sha256sum: 701da229436da073bace772a0fb9798f850f226cecc0b1f17748372e90c230d5
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
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('6018601704600055'))
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 94986)

    def test_mod0(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest/mod0.json
            sha256sum: 6ebaeb8fabecd79644db5c2505d00a7064a768606e98053de039a20f24349b46
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
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('6003600206600055'))
        #check storage
        self.assertEqual(world.get_storage_data(account_address, 0x00), 0x02)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 79986)

    def test_expPowerOf256_8(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest/expPowerOf256_8.json
            sha256sum: 7af6cc589f20e3e196ba08fe0a612d2f675d1e17fa9798abc056c234d24e3517
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
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('60086101000a600055600860ff0a60015560086101010a600255'))
        #check storage
        self.assertEqual(world.get_storage_data(account_address, 0x00), 0x010000000000000000)
        self.assertEqual(world.get_storage_data(account_address, 0x01), 0xf81bc845c81bf801)
        self.assertEqual(world.get_storage_data(account_address, 0x02), 0x01081c3846381c0801)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 39913)

    def test_addmod0(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest/addmod0.json
            sha256sum: d23739641dfba53a2391b6dbc2740580ce78576612ad280f60094560e893604e
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
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('60026002600108600055'))
        #check storage
        self.assertEqual(world.get_storage_data(account_address, 0x00), 0x01)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 79980)

    def test_expPowerOf256_23(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest/expPowerOf256_23.json
            sha256sum: 466e575aa7cb493b7c62380bab8155e83d3d29b33179ef0d3ef15cb357219bc6
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
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('60176101000a600055601760ff0a60015560176101010a600255'))
        #check storage
        self.assertEqual(world.get_storage_data(account_address, 0x00), 0x010000000000000000000000000000000000000000000000)
        self.assertEqual(world.get_storage_data(account_address, 0x01), 0xe9f63715159cc9e33a7502256eae721b304e6fea0316ff)
        self.assertEqual(world.get_storage_data(account_address, 0x02), 0x0118040e1bff182cd3afb8410f81a5092fd6939debfd1701)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 39913)

    def test_exp5(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest/exp5.json
            sha256sum: 14c276978acbc3869ae6f0d495a1712a32694f1baa20b843bed0ad2bac1f0f02
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
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('60016101010a600055'))
        #check storage
        self.assertEqual(world.get_storage_data(account_address, 0x00), 0x0101)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 79971)

    def test_expPowerOf256_18(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest/expPowerOf256_18.json
            sha256sum: 28a5da872fb61d2c29d943c3d5dbc3720aeb73d575a62a33230aa10b2cc94660
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
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('60126101000a600055601260ff0a60015560126101010a600255'))
        #check storage
        self.assertEqual(world.get_storage_data(account_address, 0x00), 0x01000000000000000000000000000000000000)
        self.assertEqual(world.get_storage_data(account_address, 0x01), 0xee95dbd2d0085a30be71f86293f0d098ee01)
        self.assertEqual(world.get_storage_data(account_address, 0x02), 0x01129c3c15c100fbac976a98a583f730991201)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 39913)

    def test_expPowerOf256_17(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest/expPowerOf256_17.json
            sha256sum: 751822d0dfc2d28bdbce613ed020159feeb46fcc188db50c05f21626fa729250
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
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('60116101000a600055601160ff0a60015560116101010a600255'))
        #check storage
        self.assertEqual(world.get_storage_data(account_address, 0x00), 0x010000000000000000000000000000000000)
        self.assertEqual(world.get_storage_data(account_address, 0x01), 0xef856134040c669755c7c022b6a77810ff)
        self.assertEqual(world.get_storage_data(account_address, 0x02), 0x01118ab1645ca45755422870354ea8881101)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 39913)

    def test_smod8_byZero(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest/smod8_byZero.json
            sha256sum: c4ecd5de35a53b50e9aea0063854e4094597d3e9730fb694159bc0b1875d678d
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
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('600d600060c86000030703600055'))
        #check storage
        self.assertEqual(world.get_storage_data(account_address, 0x00), 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff3)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 79974)

    def test_add1(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest/add1.json
            sha256sum: 39ed6bfe3de08f61ef1eadfcee209a84d717c66d208d7af9c6fb08f51094181c
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
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('60047fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff01600055'))
        #check storage
        self.assertEqual(world.get_storage_data(account_address, 0x00), 0x03)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 79988)

    def test_expPowerOf256Of256_22(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest/expPowerOf256Of256_22.json
            sha256sum: f16c8c1727641222882929af600ec5b91af30488b5f87ca1894f0cbe92296e10
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
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 1000000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('60166101000a6101000a600055601660ff0a6101000a60015560166101010a6101000a60025560166101000a60ff0a600355601660ff0a60ff0a60045560166101010a60ff0a60055560166101000a6101010a600655601660ff0a6101010a60075560166101010a6101010a600855'))
        #check storage
        self.assertEqual(world.get_storage_data(account_address, 0x03), 0x9ec55c33085514ff7f0000000000000000000000000000000000000000000001)
        self.assertEqual(world.get_storage_data(account_address, 0x04), 0xec447e662ac08957d7e290a421dbf54c0aaf43aadc9cc465ad0b02f071ea00ff)
        self.assertEqual(world.get_storage_data(account_address, 0x05), 0xdc9178d3bab470096f01477c859b5f4173986640b659426412a653465c1600ff)
        self.assertEqual(world.get_storage_data(account_address, 0x06), 0xb68fb921f7aa6aff810000000000000000000000000000000000000000000001)
        self.assertEqual(world.get_storage_data(account_address, 0x07), 0xdcf0a770777610503596ae0311af46c171151ed45107d7e7bb8f74bb5bea0101)
        self.assertEqual(world.get_storage_data(account_address, 0x08), 0x4d65773387993928c95c861274232d3fb6f6b7fe1b22e4e61a30e71172160101)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 862582)

    def test_modByZero(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest/modByZero.json
            sha256sum: 04949ae96baa5a7263e99f0f1b4b98092441009aefa96ffe5379d40f508037e5
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
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('6001600060030603600055'))
        #check storage
        self.assertEqual(world.get_storage_data(account_address, 0x00), 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 79980)

    def test_mod3(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest/mod3.json
            sha256sum: 019f392125f16c54fd42627bba52bda6d202507b8b53e73bd93e1f096a051dcb
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
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('6000600306600055'))
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 94986)

    def test_exp8(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest/exp8.json
            sha256sum: 20d1366aa59312087956f149e8ec3ad6f41ec841dfbd1f69933618a7ec0339d4
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
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('600060000a600055'))
        #check storage
        self.assertEqual(world.get_storage_data(account_address, 0x00), 0x01)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 79981)

    def test_mulmod0(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest/mulmod0.json
            sha256sum: a3e06e2b6c33d4f7c096fd12599d20523dd31037b2ad6fad82cdaa90c236d53c
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
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('60026002600109600055'))
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 94980)

    def test_expPowerOf256_27(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest/expPowerOf256_27.json
            sha256sum: 01f6a448af6bd4da88c93b9b61c1bce06d0cbd2c1bc85c540483c31be34c0c2a
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
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('601b6101000a600055601b60ff0a600155601b6101010a600255'))
        #check storage
        self.assertEqual(world.get_storage_data(account_address, 0x00), 0x01000000000000000000000000000000000000000000000000000000)
        self.assertEqual(world.get_storage_data(account_address, 0x01), 0xe653d6571cdebb270b53c9d44c40bcd425165d5af1157d6ba11aff)
        self.assertEqual(world.get_storage_data(account_address, 0x02), 0x011c6ab2cdebf906306b38bbf7d6c52648e2d6bc63859e996e5f1b01)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 39913)

    def test_mulmoddivByZero3(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest/mulmoddivByZero3.json
            sha256sum: 9e98ba30744f78d2bcc8a078826bf28bd6d409aaeeeba998734d9638a7e2309f
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
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('60006000600009600103600055'))
        #check storage
        self.assertEqual(world.get_storage_data(account_address, 0x00), 0x01)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 79974)

    def test_smod3(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest/smod3.json
            sha256sum: acb9b161d2e98cde71fce85953c352009ae76ff5cd537b484c7535a5947c7560
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
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff600260000307600055'))
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 94980)

    def test_mul3(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest/mul3.json
            sha256sum: 0c2f048cc837b06982f5e089d58179151ded6ad1ebe4519ee331cff926a5a970
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
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('6001601702600055'))
        #check storage
        self.assertEqual(world.get_storage_data(account_address, 0x00), 0x17)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 79986)

    def test_expPowerOf256_31(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest/expPowerOf256_31.json
            sha256sum: e030ce2aedc728ffd0139e74b47503c2c415cbd77d459e361ce6c9d81782a320
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
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('601f6101000a600055601f60ff0a600155601f6101010a600255'))
        #check storage
        self.assertEqual(world.get_storage_data(account_address, 0x00), 0x0100000000000000000000000000000000000000000000000000000000000000)
        self.assertEqual(world.get_storage_data(account_address, 0x01), 0xe2bfe95c5d7067567402dd9d7235fc088ac84eab8113bf8d7e3c288d2f1eff)
        self.assertEqual(world.get_storage_data(account_address, 0x02), 0x0120e30c8c1bb25c9d2219ea196c17ded3d775b231bbd28005b131fa90d11f01)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 39913)

    def test_expPowerOf256Of256_25(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest/expPowerOf256Of256_25.json
            sha256sum: dc4d976decd0f447978e378710708632547feac1e228f75d00798bc96a4fded4
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
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 1000000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('60196101000a6101000a600055601960ff0a6101000a60015560196101010a6101000a60025560196101000a60ff0a600355601960ff0a60ff0a60045560196101010a60ff0a60055560196101000a6101010a600655601960ff0a6101010a60075560196101010a6101010a600855'))
        #check storage
        self.assertEqual(world.get_storage_data(account_address, 0x03), 0x33085514ff7f0000000000000000000000000000000000000000000000000001)
        self.assertEqual(world.get_storage_data(account_address, 0x04), 0x7f510dd7198cac0a92ff7ea80451838c0dfa12114c41a0ef05907397f897feff)
        self.assertEqual(world.get_storage_data(account_address, 0x05), 0x1275e752b6aee228ecba5e9b57ef1111deff3c651e2cfbf2cccd13151f9900ff)
        self.assertEqual(world.get_storage_data(account_address, 0x06), 0x21f7aa6aff810000000000000000000000000000000000000000000000000001)
        self.assertEqual(world.get_storage_data(account_address, 0x07), 0x6646340ad51a03bb710caf05756b685b33c7dad62ae68d369243700ead99ff01)
        self.assertEqual(world.get_storage_data(account_address, 0x08), 0x29d80e8060ef2221929bb18215586c742686d6860e028ca0456b443238990101)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 862312)

    def test_expPowerOf256Of256_18(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest/expPowerOf256Of256_18.json
            sha256sum: 07f33851e18e3d0b14d72e400e1e774f4db09865875500fd8c88553d645639af
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
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 1000000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('60126101000a6101000a600055601260ff0a6101000a60015560126101010a6101000a60025560126101000a60ff0a600355601260ff0a60ff0a60045560126101010a60ff0a60055560126101000a6101010a600655601260ff0a6101010a60075560126101010a6101010a600855'))
        #check storage
        self.assertEqual(world.get_storage_data(account_address, 0x03), 0x698218879ec55c33085514ff7f00000000000000000000000000000000000001)
        self.assertEqual(world.get_storage_data(account_address, 0x04), 0x8a2cbd9f40794e2205b13306f2aa0a43c60823c64b95d8601fa4f1e521ee00ff)
        self.assertEqual(world.get_storage_data(account_address, 0x05), 0xc1b5a1e3a81da51b10d84e880f0113ff67b863ddad3faf1f4ecf413f101200ff)
        self.assertEqual(world.get_storage_data(account_address, 0x06), 0xc9b0f000b68fb921f7aa6aff8100000000000000000000000000000000000001)
        self.assertEqual(world.get_storage_data(account_address, 0x07), 0x410be68e49452a1fbcd863bf6e8d637f8eae4979c34c88d552afbcc20fee0101)
        self.assertEqual(world.get_storage_data(account_address, 0x08), 0xf540cb714754b5b1eb0373833833bd7fb0ee925ce8b92962500b7a1c22120101)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 862942)

    def test_sdiv1(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest/sdiv1.json
            sha256sum: 5f3af5c660f0ba3161afb01f4b9692764a69dc3541cc5d54256c949620be23e9
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
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff6000037fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff05600055'))
        #check storage
        self.assertEqual(world.get_storage_data(account_address, 0x00), 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 79980)

    def test_expPowerOf256Of256_5(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest/expPowerOf256Of256_5.json
            sha256sum: 74b4152feaacb01c2567ad3e3da79a8b05c170cb219fbc0eb717b12f6a587e7e
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
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 1000000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('60056101000a6101000a600055600560ff0a6101000a60015560056101010a6101000a60025560056101000a60ff0a600355600560ff0a60ff0a60045560056101010a60ff0a60055560056101000a6101010a600655600560ff0a6101010a60075560056101010a6101010a600855'))
        #check storage
        self.assertEqual(world.get_storage_data(account_address, 0x03), 0xb581ac185aad71db2d177c286929c4c22809e5dcb3085514ff7f000000000001)
        self.assertEqual(world.get_storage_data(account_address, 0x04), 0x75789eb2a64bc971389fbd11a1e6d7abbf95ad25e23fb9aa25e73a0bfc83feff)
        self.assertEqual(world.get_storage_data(account_address, 0x05), 0xfc403fa42ceb6a0d0d3321bd9b2d8af25b1b667f87a04f496c78168d078500ff)
        self.assertEqual(world.get_storage_data(account_address, 0x06), 0xcec5ec213b9cb5811f6ae00428fd7b6ef5a1af39a1f7aa6aff81000000000001)
        self.assertEqual(world.get_storage_data(account_address, 0x07), 0x70ab32233202b98d382d17713fa0be391eaf74f85ba1740c9c3238c4ed85ff01)
        self.assertEqual(world.get_storage_data(account_address, 0x08), 0xb622672a213faa79b32185ff93a7b27a8499e48f7b032cdb4d1a70300c850101)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 864112)

    def test_signextend_BitIsNotSet(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest/signextend_BitIsNotSet.json
            sha256sum: 6d8b5f865ad96787c48879dcc3e67684ae5ac46297f6cbc69e895c5b2d9e703d
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
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 1000000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('62122f6a60000b600055'))
        #check storage
        self.assertEqual(world.get_storage_data(account_address, 0x00), 0x6a)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 979986)

    def test_add2(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest/add2.json
            sha256sum: a78f969b8ee4724ddd021403e3c23b3869b111804c4cc39133ff4e7f56b087d8
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
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('60017fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff01600055'))
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 94988)

    def test_signextend_BigBytePlus1_2(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest/signextend_BigBytePlus1_2.json
            sha256sum: 09f8989882ac26cb3214654e8357ec44fa3ddeb5708810730914e3284cdd0a75
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
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 1000000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('60ff68f000000000000000010b600055'))
        #check storage
        self.assertEqual(world.get_storage_data(account_address, 0x00), 0xff)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 979986)

    def test_mulmoddivByZero1(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest/mulmoddivByZero1.json
            sha256sum: 87588fa58536cc84c65d79f21f5026034d2c57934a780d561720247816ee535b
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
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('60006001600009600055'))
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 94980)

    def test_sdiv_i256min(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest/sdiv_i256min.json
            sha256sum: 6b92f9f87c440af558aa0316466a324bb5cfd9299765402756ab0ba2f8e1ef41
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
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('60016000037f7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff60000305600055'))
        #check storage
        self.assertEqual(world.get_storage_data(account_address, 0x00), 0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 79974)

    def test_expPowerOf256_6(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest/expPowerOf256_6.json
            sha256sum: 481faa6ed50d529617e58132a7d9f63d790fa87ddcafccb458e5202045445a5d
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
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('60066101000a600055600660ff0a60015560066101010a600255'))
        #check storage
        self.assertEqual(world.get_storage_data(account_address, 0x00), 0x01000000000000)
        self.assertEqual(world.get_storage_data(account_address, 0x01), 0xfa0eec0efa01)
        self.assertEqual(world.get_storage_data(account_address, 0x02), 0x01060f140f0601)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 39913)

    def test_divByNonZero3(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest/divByNonZero3.json
            sha256sum: 4a58872388ec2dfe99cf84c30a442aec9afba2789b003880e02b8b196b66924a
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
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('6001600104600055'))
        #check storage
        self.assertEqual(world.get_storage_data(account_address, 0x00), 0x01)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 79986)

    def test_addmodDivByZero(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest/addmodDivByZero.json
            sha256sum: c83579dbcc944b7a2e1d0aa10bf3f42ac969f1bc1cb74b59eb28c0a2ad5e25f6
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
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('60006001600408600055'))
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 94980)

    def test_sdiv2(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest/sdiv2.json
            sha256sum: f52d278f9a8c0c2aa006b352241cd61b5dd1dd6eb785d12d827b0d8027108a71
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
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('6004600003600260000305600055'))
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 94974)

    def test_expPowerOf256Of256_28(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest/expPowerOf256Of256_28.json
            sha256sum: 4c859efb8c40affa585d31f7a4909b54360894e39a55388302aeb4da378b48b8
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
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 1000000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('601c6101000a6101000a600055601c60ff0a6101000a600155601c6101010a6101000a600255601c6101000a60ff0a600355601c60ff0a60ff0a600455601c6101010a60ff0a600555601c6101000a6101010a600655601c60ff0a6101010a600755601c6101010a6101010a600855'))
        #check storage
        self.assertEqual(world.get_storage_data(account_address, 0x03), 0x14ff7f0000000000000000000000000000000000000000000000000000000001)
        self.assertEqual(world.get_storage_data(account_address, 0x04), 0xffd368e44b3f85cb81ae394c9809ca9fa2db46a83d7880a912ab6d4a87e400ff)
        self.assertEqual(world.get_storage_data(account_address, 0x05), 0x0981ad53c19b15a94bcf0bf20235dd0da9df25f46ae635029fe2062e6c1c00ff)
        self.assertEqual(world.get_storage_data(account_address, 0x06), 0x6aff810000000000000000000000000000000000000000000000000000000001)
        self.assertEqual(world.get_storage_data(account_address, 0x07), 0x19df06ffa28250867006726405fbc05d43dc2f9d2f025006db089bd46be40101)
        self.assertEqual(world.get_storage_data(account_address, 0x08), 0x243fffe3a4f2982f45055c08f379648ab886da8027a7401117a8e0b8881c0101)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 862042)

    def test_signextend_0_BigByte(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest/signextend_0_BigByte.json
            sha256sum: cb7e6fcf003149071729a61168646b88f6565ec07ff0eb78723ad421e4e16f66
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
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 1000000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff60000b600055'))
        #check storage
        self.assertEqual(world.get_storage_data(account_address, 0x00), 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 979986)

    def test_expPowerOf256_5(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest/expPowerOf256_5.json
            sha256sum: 9d640e9ba8a1525eb163e409e86e534c2980f41e2b3e728c78cde48f438e1660
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
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('60056101000a600055600560ff0a60015560056101010a600255'))
        #check storage
        self.assertEqual(world.get_storage_data(account_address, 0x00), 0x010000000000)
        self.assertEqual(world.get_storage_data(account_address, 0x01), 0xfb09f604ff)
        self.assertEqual(world.get_storage_data(account_address, 0x02), 0x01050a0a0501)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 39913)

    def test_expPowerOf256Of256_4(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest/expPowerOf256Of256_4.json
            sha256sum: f317c44f06e65577e0bf55a419eedbbe34f1adfbc584fbf4849e10d8e4650817
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
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 1000000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('60046101000a6101000a600055600460ff0a6101000a60015560046101010a6101000a60025560046101000a60ff0a600355600460ff0a60ff0a60045560046101010a60ff0a60055560046101000a6101010a600655600460ff0a6101010a60075560046101010a6101010a600855'))
        #check storage
        self.assertEqual(world.get_storage_data(account_address, 0x03), 0xe6540ce46eaf70da9d644015a661e0e245b13f307cb3885514ff7f0000000001)
        self.assertEqual(world.get_storage_data(account_address, 0x04), 0x6526b38b05a6325b80e1c84ab41dc934fd70f33f1bd0eab3d1f61a4707fc00ff)
        self.assertEqual(world.get_storage_data(account_address, 0x05), 0xe959516cd27e5d8fd487b72db2989b3ec2ba9fb7ead41554526fe5a3040400ff)
        self.assertEqual(world.get_storage_data(account_address, 0x06), 0xe7498a48c6ce2530bbe814ee3440c8c44fffab7ad8a277aa6aff810000000001)
        self.assertEqual(world.get_storage_data(account_address, 0x07), 0x2dffa3e901e5a392d15b79f4193d2168147d2aa7c55870b46c3a905d03fc0101)
        self.assertEqual(world.get_storage_data(account_address, 0x08), 0xe16ea721c96539edb4f7fb82de0dad8cccb1e7a6966a6777635f6fb908040101)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 864202)

    def test_divBoostBug(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest/divBoostBug.json
            sha256sum: 5976da18430609224603cc1893ca54b1cd35d3ebf444dec3e73c8d7b2bee243a
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
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('7f01dae6076b981dae6076b981dae6076b981dae6076b981dae6076b981dae60777fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffba04600055'))
        #check storage
        self.assertEqual(world.get_storage_data(account_address, 0x00), 0x89)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 79986)

    def test_signextend_AlmostBiggestByte(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest/signextend_AlmostBiggestByte.json
            sha256sum: 11c4b52c510865f61c220340d2e18a7e5cfdf036ad952d96f39923215243a10e
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
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 1000000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0b600055'))
        #check storage
        self.assertEqual(world.get_storage_data(account_address, 0x00), 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 979986)

    def test_sdiv_i256min2(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest/sdiv_i256min2.json
            sha256sum: 275449b4f1f2f5e136aa4002228f6564e7817d15f202403cc83b1954dc853edc
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
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('60016000037f800000000000000000000000000000000000000000000000000000000000000060000305600055'))
        #check storage
        self.assertEqual(world.get_storage_data(account_address, 0x00), 0x8000000000000000000000000000000000000000000000000000000000000000)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 79974)

    def test_divByNonZero2(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest/divByNonZero2.json
            sha256sum: 7142961a2fe9bb460cf5b9ccb738fd15610f3e3e6d179799baea2e9cd0bb707a
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
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('6018600004600055'))
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 94986)

    def test_expPowerOf256Of256_13(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest/expPowerOf256Of256_13.json
            sha256sum: 95207c56f72b02af2a75ccc0e93b71bb8abed7278b79f7b75bcd3c3c85419cc1
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
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 1000000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('600d6101000a6101000a600055600d60ff0a6101000a600155600d6101010a6101000a600255600d6101000a60ff0a600355600d60ff0a60ff0a600455600d6101010a60ff0a600555600d6101000a6101010a600655600d60ff0a6101010a600755600d6101010a6101010a600855'))
        #check storage
        self.assertEqual(world.get_storage_data(account_address, 0x03), 0xe02639036c698218879ec55c33085514ff7f0000000000000000000000000001)
        self.assertEqual(world.get_storage_data(account_address, 0x04), 0x8be664bde946d939ce551b948b503787942d2a7734509288c1b62fd5c48bfeff)
        self.assertEqual(world.get_storage_data(account_address, 0x05), 0xa923a28e7a75aef26c51580ffc686879e4a0b404b089bdbcd751d88b478d00ff)
        self.assertEqual(world.get_storage_data(account_address, 0x06), 0x41ac5ea30fc9b0f000b68fb921f7aa6aff810000000000000000000000000001)
        self.assertEqual(world.get_storage_data(account_address, 0x07), 0x0daa3a177ec975cb69bb4acf4a6e1be7bcc1ad33d1ffad97510f9fea9d8dff01)
        self.assertEqual(world.get_storage_data(account_address, 0x08), 0x19e6822beb889be28310060f4fb9741bfd50a31fa81ec65de21f7b02548d0101)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 863392)

    def test_mulmod4(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest/mulmod4.json
            sha256sum: 6e8816ebf4f722e23f390b324031767ab72f689c83ed9b6702e177d5dae01af8
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
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('6064601b60250960005360006001f3'))
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 99968)

    def test_smod0(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest/smod0.json
            sha256sum: 6498d134fdc150387eb998a76be2b77ceefaa893e22084d1a8fe112a33e35325
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
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('6003600003600560000307600055'))
        #check storage
        self.assertEqual(world.get_storage_data(account_address, 0x00), 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 79974)

    def test_expPowerOf256Of256_24(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest/expPowerOf256Of256_24.json
            sha256sum: 1736bdb3853b7d445199878cabd90e496d1ddfaf1b49fc3327e699d5dcdc85ec
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
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 1000000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('60186101000a6101000a600055601860ff0a6101000a60015560186101010a6101000a60025560186101000a60ff0a600355601860ff0a60ff0a60045560186101010a60ff0a60055560186101000a6101010a600655601860ff0a6101010a60075560186101010a6101010a600855'))
        #check storage
        self.assertEqual(world.get_storage_data(account_address, 0x03), 0x5c33085514ff7f00000000000000000000000000000000000000000000000001)
        self.assertEqual(world.get_storage_data(account_address, 0x04), 0xd542e526003539ead104274aff2d78332366e29d328c2161f0c120731fe800ff)
        self.assertEqual(world.get_storage_data(account_address, 0x05), 0xc706cb25e8384ce9bb5c9cb48415238ba03e16c448e292c0a101843b081800ff)
        self.assertEqual(world.get_storage_data(account_address, 0x06), 0xb921f7aa6aff8100000000000000000000000000000000000000000000000001)
        self.assertEqual(world.get_storage_data(account_address, 0x07), 0x4ca55f89202c524cb0f1cb3195d13c8d94a9f7a05c59e1d4031577c707e80101)
        self.assertEqual(world.get_storage_data(account_address, 0x08), 0x8c4b0574e9156b80035f3ecdcf1fe79d273ed7559747a4322bcd338f20180101)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 862402)

    def test_mulmoddivByZero2(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest/mulmoddivByZero2.json
            sha256sum: ea207a1d3835264e9a68fdb56b4a1507b95499dfd32cb5d8429e4ad151c0dd15
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
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('60006000600109600055'))
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 94980)

    def test_sub0(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest/sub0.json
            sha256sum: 103dbce99c97e984c1b91c1a9a0f1eb0bf16d2f2f687c48bebbc7b3471bb1efd
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
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('6001601703600055'))
        #check storage
        self.assertEqual(world.get_storage_data(account_address, 0x00), 0x16)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 79988)

    def test_mulmoddivByZero(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest/mulmoddivByZero.json
            sha256sum: 65f743c22aad82664e0138c95ee88925bd2280010c83e03149cabec8765abfed
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
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('60006001600509600055'))
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 94980)

    def test_mulmod2(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest/mulmod2.json
            sha256sum: 5c1082992a703772d55a0738b0d6773e2e687a1c245952fbde8f0e63cd318497
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
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('60036001600560000309600055'))
        #check storage
        self.assertEqual(world.get_storage_data(account_address, 0x00), 0x02)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 79974)

    def test_expPowerOf256Of256_1(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest/expPowerOf256Of256_1.json
            sha256sum: f36b954cc8c062b93aabaadc89f3e8a7feaeeb5ca923f3da45babd45b176567c
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
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 1000000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('60016101000a6101000a600055600160ff0a6101000a60015560016101010a6101000a60025560016101000a60ff0a600355600160ff0a60ff0a60045560016101010a60ff0a60055560016101000a6101010a600655600160ff0a6101010a60075560016101010a6101010a600855'))
        #check storage
        self.assertEqual(world.get_storage_data(account_address, 0x03), 0x06c3acd330b959ad6efabce6d2d2125e73a88a65a9880d203dddf5957f7f0001)
        self.assertEqual(world.get_storage_data(account_address, 0x04), 0x8f965a06da0ac41dcb3a34f1d8ab7d8fee620a94faa42c395997756b007ffeff)
        self.assertEqual(world.get_storage_data(account_address, 0x05), 0xbce9265d88a053c18bc229ebff404c1534e1db43de85131da0179fe9ff8100ff)
        self.assertEqual(world.get_storage_data(account_address, 0x06), 0x02b5e9d7a094c19f5ebdd4f2e618f859ed15e4f1f0351f286bf849eb7f810001)
        self.assertEqual(world.get_storage_data(account_address, 0x07), 0xc73b7a6f68385c653a24993bb72eea0e4ba17470816ec658cf9c5bedfd81ff01)
        self.assertEqual(world.get_storage_data(account_address, 0x08), 0xb89fc178355660fe1c92c7d8ff11524702fad6e2255447946442356b00810101)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 864472)

    def test_expPowerOf256Of256_11(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest/expPowerOf256Of256_11.json
            sha256sum: 0e1a60ae4742d00ddd3ad530f52dee273de1f9bfbb2c49f2104ea3dff0acf428
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
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 1000000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('600b6101000a6101000a600055600b60ff0a6101000a600155600b6101010a6101000a600255600b6101000a60ff0a600355600b60ff0a60ff0a600455600b6101010a60ff0a600555600b6101000a6101010a600655600b60ff0a6101010a600755600b6101010a6101010a600855'))
        #check storage
        self.assertEqual(world.get_storage_data(account_address, 0x03), 0xe1440264b8ee0cea0218879ec55c33085514ff7f000000000000000000000001)
        self.assertEqual(world.get_storage_data(account_address, 0x04), 0x29575fdce377b23043e489e358581474bc863187fa85f9945473a2be5889feff)
        self.assertEqual(world.get_storage_data(account_address, 0x05), 0x3df8c030ec521fb109c4d887dbbc14c7c9c9921b27058e3503971b60b18b00ff)
        self.assertEqual(world.get_storage_data(account_address, 0x06), 0x67799740340daf4a30f000b68fb921f7aa6aff81000000000000000000000001)
        self.assertEqual(world.get_storage_data(account_address, 0x07), 0x540a4e4635b40585e09ff10b63ffe310dd717fca5c0a51570091e25e378bff01)
        self.assertEqual(world.get_storage_data(account_address, 0x08), 0xdbbaef5c49ffee61b08cde6ebc8dba6e9a62d56c2355d1980cb9e790bc8b0101)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 863572)

    def test_addmod1_overflow3(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest/addmod1_overflow3.json
            sha256sum: a56baceb104b28e87308de976a7b7bbe6a4b72cbfd1d71856b9e913a3b9c253f
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
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 1000000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('60056001600160000308600055'))
        #check storage
        self.assertEqual(world.get_storage_data(account_address, 0x00), 0x01)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 979974)

    def test_exp4(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest/exp4.json
            sha256sum: c00d2d7becce1d1c66100d2e9ebb08d7da648fb314457a9bd152b4b045016859
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
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('6000637fffffff0a600055'))
        #check storage
        self.assertEqual(world.get_storage_data(account_address, 0x00), 0x01)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 79981)

    def test_expPowerOf256_29(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest/expPowerOf256_29.json
            sha256sum: 582ea7698c7827b15975d904e17f12de20f099ad18cb59685093ac1d90a7209f
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
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('601d6101000a600055601d60ff0a600155601d6101010a600255'))
        #check storage
        self.assertEqual(world.get_storage_data(account_address, 0x00), 0x010000000000000000000000000000000000000000000000000000000000)
        self.assertEqual(world.get_storage_data(account_address, 0x01), 0xe48814fe44fc1a8f78642d946d7c879b39a055b6988e438647446a1cff)
        self.assertEqual(world.get_storage_data(account_address, 0x02), 0x011ea4a49e3a9ee435d23f98a8826a875a9ae54cb3090d5c3fd547961d01)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 39913)

    def test_mul5(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest/mul5.json
            sha256sum: 1e2ce3255dac28473f8418248bc39d8215f47956475bbf62cf9e1615fabfdeca
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
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('7f80000000000000000000000000000000000000000000000000000000000000007f800000000000000000000000000000000000000000000000000000000000000002600055'))
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 94986)

    def test_expPowerOf256_32(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest/expPowerOf256_32.json
            sha256sum: 0eeb3e3ee41de713ccc847cb74d37a09e55c7aca98a3d3d62750dc6609480904
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
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('60206101000a600055602060ff0a60015560206101010a600255'))
        #check storage
        self.assertEqual(world.get_storage_data(account_address, 0x01), 0xe1dd29730112f6ef1d8edabfd4c3c60c823d865cd592abcdf0bdec64a1efe001)
        self.assertEqual(world.get_storage_data(account_address, 0x02), 0x2203ef98a7ce0ef9bf3c04038583f6b2ab4d27e3ed8e5285b6e32c8b61f02001)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 54913)

    def test_expPowerOf256Of256_7(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest/expPowerOf256Of256_7.json
            sha256sum: c5bb55bbbd3503e3e352d0f578be5016d005da8f3329408792cb3c1c1390eef2
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
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 1000000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('60076101000a6101000a600055600760ff0a6101000a60015560076101010a6101000a60025560076101000a60ff0a600355600760ff0a60ff0a60045560076101010a60ff0a60055560076101000a6101010a600655600760ff0a6101010a60075560076101010a6101010a600855'))
        #check storage
        self.assertEqual(world.get_storage_data(account_address, 0x03), 0x8bb02654111ad8c60ad8af132283a81f455c33085514ff7f0000000000000001)
        self.assertEqual(world.get_storage_data(account_address, 0x04), 0xa8f75c129dbb8466d6703a2a0b8212131b3248d70e2478862ac40fe17485feff)
        self.assertEqual(world.get_storage_data(account_address, 0x05), 0x5fd4d2de580383ee59f5e800ddb3f1717ceae03aede19d3dec5e5a69918700ff)
        self.assertEqual(world.get_storage_data(account_address, 0x06), 0xc8624230b524b85d6340da48a5db20370fb921f7aa6aff810000000000000001)
        self.assertEqual(world.get_storage_data(account_address, 0x07), 0x287b58a5a13cd7f454468ca616c181712f5ed25433a7d5a894b6ced35f87ff01)
        self.assertEqual(world.get_storage_data(account_address, 0x08), 0x09930d11ac2804fa977bf951593c8dff8498779cc0cdc5812a4fba2f98870101)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 863932)

    def test_expPowerOf256Of256_23(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest/expPowerOf256Of256_23.json
            sha256sum: 6eeaf2c7bab4d794c33640d2884efd5b3cd2874871ab7a89331aa6edf20c03d1
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
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 1000000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('60176101000a6101000a600055601760ff0a6101000a60015560176101010a6101000a60025560176101000a60ff0a600355601760ff0a60ff0a60045560176101010a60ff0a60055560176101000a6101010a600655601760ff0a6101010a60075560176101010a6101010a600855'))
        #check storage
        self.assertEqual(world.get_storage_data(account_address, 0x03), 0xc55c33085514ff7f000000000000000000000000000000000000000000000001)
        self.assertEqual(world.get_storage_data(account_address, 0x04), 0x537ca0f03f974303005f1e6693b55b72315a166841732e42b8353724a495feff)
        self.assertEqual(world.get_storage_data(account_address, 0x05), 0x86418797ec60058de6cca47dfdbee79923ac49d7801e01840041ca76719700ff)
        self.assertEqual(world.get_storage_data(account_address, 0x06), 0x8fb921f7aa6aff81000000000000000000000000000000000000000000000001)
        self.assertEqual(world.get_storage_data(account_address, 0x07), 0x56a55341ab8d4318f1cfb55d5f21e2ba35d7e070a72bac6b2b21baae5f97ff01)
        self.assertEqual(world.get_storage_data(account_address, 0x08), 0x55ddd0ec77909de6d8311116cf520398e816f928b06fdd90ec239d0488970101)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 862492)

    def test_smod_i256min1(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest/smod_i256min1.json
            sha256sum: c468a1fb47af46e0b20ee86cf9de8467fc3247f655d6b4505e05d7b00c0054d9
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
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('60016000037f800000000000000000000000000000000000000000000000000000000000000060000307600055'))
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 94974)

    def test_smod_i256min2(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest/smod_i256min2.json
            sha256sum: 68938b6c032c53ff92c9c0a22f763add54fc7b084ffa9a87107f5fad9aa3293e
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
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('600160016000037f80000000000000000000000000000000000000000000000000000000000000006000030703600055'))
        #check storage
        self.assertEqual(world.get_storage_data(account_address, 0x00), 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 79968)

    def test_smod7(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest/smod7.json
            sha256sum: 7faf08ca921b8ecd4a28f104a2294df5ec333c852528b139c2a91ebc84c8ff6c
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
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 10000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7f7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff60000307600055'))
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 4980)

    def test_expPowerOf256Of256_31(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest/expPowerOf256Of256_31.json
            sha256sum: e653dd69e7a87f875c091b4406a527a582bbdb17751dc5845d9aa94ea2870523
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
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 1000000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('601f6101000a6101000a600055601f60ff0a6101000a600155601f6101010a6101000a600255601f6101000a60ff0a600355601f60ff0a60ff0a600455601f6101010a60ff0a600555601f6101000a6101010a600655601f60ff0a6101010a600755601f6101010a6101010a600855'))
        #check storage
        self.assertEqual(world.get_storage_data(account_address, 0x03), 0x01)
        self.assertEqual(world.get_storage_data(account_address, 0x04), 0xf9cb87f5b1ab58602f52a1e9d392e5675b86a59a53943a8d4ec2a915dc9dfeff)
        self.assertEqual(world.get_storage_data(account_address, 0x05), 0x893d729a64e318860ec5047e70e598da163eb41e71e74b04dfd4712d419f00ff)
        self.assertEqual(world.get_storage_data(account_address, 0x06), 0x01)
        self.assertEqual(world.get_storage_data(account_address, 0x07), 0xee5f2839c1b4f6ca05e6fdb04e2fb49c0f860b3765c27dc781a150cb7f9fff01)
        self.assertEqual(world.get_storage_data(account_address, 0x08), 0xb4c358e3c6bcddfb509ea487d733df0e1854f29c3b6bfd4a8caabe3f609f0101)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 861772)

    def test_mul2(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest/mul2.json
            sha256sum: deb770397bc42ee427979491805bbc0c7bf38da6bf6548b04ac8ddb536efb62f
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
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('6017600002600055'))
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 94986)

    def test_addmod1(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest/addmod1.json
            sha256sum: fe6b30fa58ddaa51b9d6588bd04bfc8a0552e5fd05032a7b7c1a750ee4164d9f
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
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('60026002600003600160000308600055'))
        #check storage
        self.assertEqual(world.get_storage_data(account_address, 0x00), 0x01)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 79968)

    def test_expPowerOf256Of256_15(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest/expPowerOf256Of256_15.json
            sha256sum: 1ad5207e318e5d4f2304867f113e7eee32a473979b36964c1127366449e194c0
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
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 1000000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('600f6101000a6101000a600055600f60ff0a6101000a600155600f6101010a6101000a600255600f6101000a60ff0a600355600f60ff0a60ff0a600455600f6101010a60ff0a600555600f6101000a6101010a600655600f60ff0a6101010a600755600f6101010a6101010a600855'))
        #check storage
        self.assertEqual(world.get_storage_data(account_address, 0x03), 0x9882ec698218879ec55c33085514ff7f00000000000000000000000000000001)
        self.assertEqual(world.get_storage_data(account_address, 0x04), 0x75c4915e18b96704209738f5ca765568bb4dc4113d56683977825a132c8dfeff)
        self.assertEqual(world.get_storage_data(account_address, 0x05), 0x5c76839bf5a80b1da705dbdf43e4dd6770cd7501af11ff2dab7918dfe18f00ff)
        self.assertEqual(world.get_storage_data(account_address, 0x06), 0xbf228fc9b0f000b68fb921f7aa6aff8100000000000000000000000000000001)
        self.assertEqual(world.get_storage_data(account_address, 0x07), 0xc6a29131e7594004bc2aa79f0d2c402a1409c57c77d284c14b1a3ab0ff8fff01)
        self.assertEqual(world.get_storage_data(account_address, 0x08), 0xe6b3e5cf6ec90e532fef7d08455ebf92a03e9e3f6e224ea0febdf1a9f08f0101)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 863212)

    def test_expPowerOf2_16(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest/expPowerOf2_16.json
            sha256sum: b58c1e04e1e2d66fe93b4101623323ede23612254483fa10460e4cb5e9f8b8f9
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
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('601060020a600055600f60020a600155601160020a600255'))
        #check storage
        self.assertEqual(world.get_storage_data(account_address, 0x00), 0x010000)
        self.assertEqual(world.get_storage_data(account_address, 0x01), 0x8000)
        self.assertEqual(world.get_storage_data(account_address, 0x02), 0x020000)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 39913)

    def test_expPowerOf256Of256_2(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest/expPowerOf256Of256_2.json
            sha256sum: 58b00fbc79c0666213dfa8c39bb1a2d05a09a5cffccd82137035d06d9f0a877e
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
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 1000000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('60026101000a6101000a600055600260ff0a6101000a60015560026101010a6101000a60025560026101000a60ff0a600355600260ff0a60ff0a60045560026101010a60ff0a60055560026101000a6101010a600655600260ff0a6101010a60075560026101010a6101010a600855'))
        #check storage
        self.assertEqual(world.get_storage_data(account_address, 0x03), 0x4ee4ceeaac565c81f55a87c43f82f7c889ef4fc7c679671e28d594ff7f000001)
        self.assertEqual(world.get_storage_data(account_address, 0x04), 0x82f46a1b4e34d66712910615d2571d75606ceac51fa8ca8c58cf6ca881fe00ff)
        self.assertEqual(world.get_storage_data(account_address, 0x05), 0x81c9fcefa5de158ae2007f25d35c0d11cd735342a48905955a5a6852800200ff)
        self.assertEqual(world.get_storage_data(account_address, 0x06), 0x666ac362902470ed850709e2a29969d10cba09debc03c38d172aeaff81000001)
        self.assertEqual(world.get_storage_data(account_address, 0x07), 0xeb30a3c678a01bde914548f98f3366dc0ffe9f85384ebf1111d03dad7ffe0101)
        self.assertEqual(world.get_storage_data(account_address, 0x08), 0x72d0a7939b6303ce1d46e6e3f1b8be303bfdb2b00f41ad8076b0975782020101)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 864382)

    def test_fibbonacci_unrolled(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest/fibbonacci_unrolled.json
            sha256sum: cf38c8cba03d5c8476586307e6dae5f6d81cb27a1e2a541bf541f186676ec409
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
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 1000000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('6001600181810181810181810181810181810181810181810181810181810181810181810181810181810181810181810181810181810160005260206000f3'))
        #check outs
        self.assertEqual(returndata, unhexlify('0000000000000000000000000000000000000000000000000000000000001055'))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 999826)

    def test_mulmod1_overflow(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest/mulmod1_overflow.json
            sha256sum: fcf46cc346ac01287ddb9fb297f0dced373655a45a6785d0681bb344fc53167c
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
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 10000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('60056002600160000309600055'))
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 4974)

    def test_mulUnderFlow(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest/mulUnderFlow.json
            sha256sum: 070e1e03d092c4327cca0880e2a1d2631d900b5972c91b4727a19d14a2ca90b2
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
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                new_vm.execute()
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
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest/signextend_bitIsSet.json
            sha256sum: 871e3fa32dfca5bf9b94eb00dfd20a85437e9b7d1958fb3d51b1990c5ee18952
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
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 1000000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('62122ff460000b600055'))
        #check storage
        self.assertEqual(world.get_storage_data(account_address, 0x00), 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff4)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 979986)

    def test_divByZero_2(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest/divByZero_2.json
            sha256sum: e487f00451e53508daea18a896d666c8e76d1d1e28128f0ceea1aef5ca74a497
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
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('60076000600d0401600055'))
        #check storage
        self.assertEqual(world.get_storage_data(account_address, 0x00), 0x07)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 79980)

    def test_expPowerOf256Of256_14(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest/expPowerOf256Of256_14.json
            sha256sum: 5bbd8b096b65a3385978b4a0b4d5c2acc5c81ec90f1d62d0bf3633f212265f31
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
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 1000000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('600e6101000a6101000a600055600e60ff0a6101000a600155600e6101010a6101000a600255600e6101000a60ff0a600355600e60ff0a60ff0a600455600e6101010a60ff0a600555600e6101000a6101010a600655600e60ff0a6101010a600755600e6101010a6101010a600855'))
        #check storage
        self.assertEqual(world.get_storage_data(account_address, 0x03), 0xdb9902ec698218879ec55c33085514ff7f000000000000000000000000000001)
        self.assertEqual(world.get_storage_data(account_address, 0x04), 0x83fab06c6c8fef761ebbb9534c06ac2a9d61820623008069062ff3b1e1f200ff)
        self.assertEqual(world.get_storage_data(account_address, 0x05), 0x3f791dd183ed5b963bd86e0dba1a9dd5b8ceeb078f15c73062f1942fd40e00ff)
        self.assertEqual(world.get_storage_data(account_address, 0x06), 0xe0bfa28fc9b0f000b68fb921f7aa6aff81000000000000000000000000000001)
        self.assertEqual(world.get_storage_data(account_address, 0x07), 0x8133b760dfae27560eb490f235ddfa301f058dee4f01f3fe4b3567d0d3f20101)
        self.assertEqual(world.get_storage_data(account_address, 0x08), 0xcd4cd0124e983af71620fb5f98275965c6a8bebc4b8adc288b63224ee20e0101)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 863302)

    def test_expPowerOf2_128(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest/expPowerOf2_128.json
            sha256sum: 631af10d4fc90f573498ed45f56b631f027895b9a0fedde7ebc86ef7bb40eace
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
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('608060020a600055607f60020a600155608160020a600255'))
        #check storage
        self.assertEqual(world.get_storage_data(account_address, 0x00), 0x0100000000000000000000000000000000)
        self.assertEqual(world.get_storage_data(account_address, 0x01), 0x80000000000000000000000000000000)
        self.assertEqual(world.get_storage_data(account_address, 0x02), 0x0200000000000000000000000000000000)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 39913)

    def test_sdiv7(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest/sdiv7.json
            sha256sum: 559bb1d011595b5835337162a9f85a2b1b8711b34ca5c999ec3c088ee71fe0a4
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
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('6019600160000305600055'))
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 94980)

    def test_sdiv_i256min3(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest/sdiv_i256min3.json
            sha256sum: 43473a87fdde5b9341bef07ccb77344dc2eff16cf0e7cd99c10d645260f811d4
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
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x1
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 1000000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('7f7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff6000037fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff05600055'))
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 994980)

    def test_sdiv3(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest/sdiv3.json
            sha256sum: 22d2384cf5dc07b077bc5b7e3d946e85a7d78238a806b447527452fb5511bf57
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
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('6002600003600405600055'))
        #check storage
        self.assertEqual(world.get_storage_data(account_address, 0x00), 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 79980)

    def test_expPowerOf256Of256_16(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest/expPowerOf256Of256_16.json
            sha256sum: 54dd54a397016780c6019d51008d5d64e83f4ca889c226c76f724881bab90bb9
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
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 1000000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('60106101000a6101000a600055601060ff0a6101000a60015560106101010a6101000a60025560106101000a60ff0a600355601060ff0a60ff0a60045560106101010a60ff0a60055560106101000a6101010a600655601060ff0a6101010a60075560106101010a6101010a600855'))
        #check storage
        self.assertEqual(world.get_storage_data(account_address, 0x03), 0x82ec698218879ec55c33085514ff7f0000000000000000000000000000000001)
        self.assertEqual(world.get_storage_data(account_address, 0x04), 0x3122f4bcdf6dd8b265cd18eb6af28c879aed44a35e0bf59273e39e6c7ff000ff)
        self.assertEqual(world.get_storage_data(account_address, 0x05), 0x6a2b3bc87a02c29b9d27757df43047ecd0f15485270fca27417a701c701000ff)
        self.assertEqual(world.get_storage_data(account_address, 0x06), 0x228fc9b0f000b68fb921f7aa6aff810000000000000000000000000000000001)
        self.assertEqual(world.get_storage_data(account_address, 0x07), 0x88e1259502eef93d46060aacc9e2ff506c734dade0b6714ab12d17e46ff00101)
        self.assertEqual(world.get_storage_data(account_address, 0x08), 0x4a103813c12c12169b218296bb0a9eae80cf8d2b158aa70eb990f99480100101)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 863122)

    def test_expPowerOf256_2(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest/expPowerOf256_2.json
            sha256sum: 5ef6219ad013a2937f3e14b6b0c68626f36393fec3df0fc9f22e28a2a2715230
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
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('60026101000a600055600260ff0a60015560026101010a600255'))
        #check storage
        self.assertEqual(world.get_storage_data(account_address, 0x00), 0x010000)
        self.assertEqual(world.get_storage_data(account_address, 0x01), 0xfe01)
        self.assertEqual(world.get_storage_data(account_address, 0x02), 0x010201)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 39913)

    def test_expPowerOf2_32(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest/expPowerOf2_32.json
            sha256sum: 6fc82d32665481c8f76569e0d67ccff957efccb55de4c9e1aed99ba1e5ac87cc
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
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('602060020a600055601f60020a600155602160020a600255'))
        #check storage
        self.assertEqual(world.get_storage_data(account_address, 0x00), 0x0100000000)
        self.assertEqual(world.get_storage_data(account_address, 0x01), 0x80000000)
        self.assertEqual(world.get_storage_data(account_address, 0x02), 0x0200000000)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 39913)

    def test_signextend_BigByteBigByte(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest/signextend_BigByteBigByte.json
            sha256sum: 2176e3e0767abb98f8087efa91e73a0f167b6905b087ede284b95665add606a7
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
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 1000000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0b600055'))
        #check storage
        self.assertEqual(world.get_storage_data(account_address, 0x00), 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 979986)

    def test_expPowerOf256_19(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest/expPowerOf256_19.json
            sha256sum: dfba34ee601d99d718902addd48a377bbfa732240772c33c5ce78e3ef45ebda3
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
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('60136101000a600055601360ff0a60015560136101010a600255'))
        #check storage
        self.assertEqual(world.get_storage_data(account_address, 0x00), 0x0100000000000000000000000000000000000000)
        self.assertEqual(world.get_storage_data(account_address, 0x01), 0xeda745f6fd3851d68db3866a315cdfc85512ff)
        self.assertEqual(world.get_storage_data(account_address, 0x02), 0x0113aed851d6c1fca84402033e297b27c9ab1301)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 39913)

    def test_mulmod1_overflow2(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest/mulmod1_overflow2.json
            sha256sum: 07b379cea2c1c0d5dd094752624fbdd941dfea3f88f4c562d847db5e20ab07c5
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
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 1000000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('600560027f800000000000000000000000000000000000000000000000000000000000000009600055'))
        #check storage
        self.assertEqual(world.get_storage_data(account_address, 0x00), 0x01)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 979980)

    def test_smod6(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest/smod6.json
            sha256sum: 2b04a74535675b5da3287b948339f33c55cfa84dcdb27552830e45ab004e2098
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
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('7f7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff60000307600055'))
        #check storage
        self.assertEqual(world.get_storage_data(account_address, 0x00), 0x01)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 79980)

    def test_addmod2_0(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest/addmod2_0.json
            sha256sum: 85fb121305be12bcdc7f743f2b392e0c4c4cc31b7104513f2c8533c33185d81e
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
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('60036001600660000308600360056000030714600055'))
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 94954)

    def test_expXY_success(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest/expXY_success.json
            sha256sum: b315dbaf994c4d98f223ac1f23ff3d4d5478a7273567d561db89eae32d481a2e
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
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = unhexlify('0000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000f')
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('6000356000556020356001556001546000540a600255'))
        #check storage
        self.assertEqual(world.get_storage_data(account_address, 0x00), 0x02)
        self.assertEqual(world.get_storage_data(account_address, 0x01), 0x0f)
        self.assertEqual(world.get_storage_data(account_address, 0x02), 0x8000)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 39853)

    def test_smod5(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest/smod5.json
            sha256sum: 85a792fa7cfea6a48b311f08c82bb8e7c198195df4f954b70fe8d7070d970d74
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
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 10000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('7f7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7f7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff60000307600055'))
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 4980)

    def test_expPowerOf256_25(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest/expPowerOf256_25.json
            sha256sum: 057b7769b10b1c0f0dc6c25e8a9c56f0d8baf951ec5f90fee06150d870775b38
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
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('60196101000a600055601960ff0a60015560196101010a600255'))
        #check storage
        self.assertEqual(world.get_storage_data(account_address, 0x00), 0x0100000000000000000000000000000000000000000000000000)
        self.assertEqual(world.get_storage_data(account_address, 0x01), 0xe823349d2286a5ec3de3529625f683e56c0903589efad418ff)
        self.assertEqual(world.get_storage_data(account_address, 0x02), 0x011a352e3c45325c4583eb6149e1b7d4e73f709bbb72fd2c1901)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 39913)

    def test_mul6(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest/mul6.json
            sha256sum: 57838699eab6c64f74c925c295f062f7427384cb7dc029621331612c79289ec1
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
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('7f7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7f7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff02600055'))
        #check storage
        self.assertEqual(world.get_storage_data(account_address, 0x00), 0x01)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 79986)

    def test_div1(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest/div1.json
            sha256sum: f7f6f4eaf35a0fd06ca09498989d490c721f7b89b8d79156b65b5644040c363a
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
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('60027ffedcba9876543210fedcba9876543210fedcba9876543210fedcba98765432100460005260206000f3'))
        #check outs
        self.assertEqual(returndata, unhexlify('7f6e5d4c3b2a19087f6e5d4c3b2a19087f6e5d4c3b2a19087f6e5d4c3b2a1908'))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 99974)

    def test_expPowerOf256Of256_21(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest/expPowerOf256Of256_21.json
            sha256sum: 1f307e64b0374885a9dc86f5ee971835505e4dc58ea73392256cc03b0d29bad2
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
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 1000000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('60156101000a6101000a600055601560ff0a6101000a60015560156101010a6101000a60025560156101000a60ff0a600355601560ff0a60ff0a60045560156101010a60ff0a60055560156101000a6101010a600655601560ff0a6101010a60075560156101010a6101010a600855'))
        #check storage
        self.assertEqual(world.get_storage_data(account_address, 0x03), 0x879ec55c33085514ff7f00000000000000000000000000000000000000000001)
        self.assertEqual(world.get_storage_data(account_address, 0x04), 0x7fd07055ff50cdfe4b4bd9a15133d72d3607d92eb7ac81bac93db7ff4c93feff)
        self.assertEqual(world.get_storage_data(account_address, 0x05), 0x665ac5c769e87f61d5993abc26522fbfca2734d76a63216b2d550d29c79500ff)
        self.assertEqual(world.get_storage_data(account_address, 0x06), 0xb68fb921f7aa6aff8100000000000000000000000000000000000000000001)
        self.assertEqual(world.get_storage_data(account_address, 0x07), 0x1c93db67c9884bc694686d69a25a5d7ed089841d5ce147fdd7199ab00d95ff01)
        self.assertEqual(world.get_storage_data(account_address, 0x08), 0x485053d8ff66be52036597520344fac87b6a305426a9e49221d3f934dc950101)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 862672)

    def test_expPowerOf256Of256_20(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest/expPowerOf256Of256_20.json
            sha256sum: c61d4fd03c79394b74162ca600b43af2c2499a7e05cbccc2454abf4056113386
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
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 1000000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('60146101000a6101000a600055601460ff0a6101000a60015560146101010a6101000a60025560146101000a60ff0a600355601460ff0a60ff0a60045560146101010a60ff0a60055560146101000a6101010a600655601460ff0a6101010a60075560146101010a6101010a600855'))
        #check storage
        self.assertEqual(world.get_storage_data(account_address, 0x03), 0x18879ec55c33085514ff7f000000000000000000000000000000000000000001)
        self.assertEqual(world.get_storage_data(account_address, 0x04), 0x67e4797dc21f02ce4a7c52218c7dbea5d212e6c244e24f0ba4c08613c7ec00ff)
        self.assertEqual(world.get_storage_data(account_address, 0x05), 0xa1ce1a085f258785846939cc1d2e8725ac94ad4dff8913234e00679fb41400ff)
        self.assertEqual(world.get_storage_data(account_address, 0x06), 0xf000b68fb921f7aa6aff81000000000000000000000000000000000000000001)
        self.assertEqual(world.get_storage_data(account_address, 0x07), 0xcce501857a1cb45473915a28082af950e0f78f7e2de68ce748adb661b3ec0101)
        self.assertEqual(world.get_storage_data(account_address, 0x08), 0x3b2e28d274a16c08b58a23bad63bba6d7b09685769d1f68ca3873bedc8140101)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 862762)

    def test_mulmod3(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest/mulmod3.json
            sha256sum: b95744cfc6202391c10769e39feaf834d79404bd7934a2be24899f419ace4edf
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
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('60036000036001600509600055'))
        #check storage
        self.assertEqual(world.get_storage_data(account_address, 0x00), 0x05)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 79974)

    def test_mulmod1_overflow3(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest/mulmod1_overflow3.json
            sha256sum: be1ba99100db055a08d2b485c39b4029be4ff7b21ec81087a17249fa228808f1
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
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 1000000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('600560027f7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff09600055'))
        #check storage
        self.assertEqual(world.get_storage_data(account_address, 0x00), 0x04)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 979980)

    def test_sub1(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest/sub1.json
            sha256sum: 170b66d4b6b802237c5055c02681320e277e23694e7799a67f00314fed980c19
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
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('6003600203600055'))
        #check storage
        self.assertEqual(world.get_storage_data(account_address, 0x00), 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 79988)

    def test_sdiv6(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest/sdiv6.json
            sha256sum: 6517f9859fd0dc4a455c1084ac9a6296f4f2b20604371225a1c29c12409af716
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
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('60007f800000000000000000000000000000000000000000000000000000000000000060000305600055'))
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 94980)

    def test_expPowerOf256Of256_12(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest/expPowerOf256Of256_12.json
            sha256sum: 1d00cf69522c945659a07018b8318fb98f9ccb8e4a345fb068a5bd700e28c0d7
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
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 1000000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('600c6101000a6101000a600055600c60ff0a6101000a600155600c6101010a6101000a600255600c6101000a60ff0a600355600c60ff0a60ff0a600455600c6101010a60ff0a600555600c6101000a6101010a600655600c60ff0a6101010a600755600c6101010a6101010a600855'))
        #check storage
        self.assertEqual(world.get_storage_data(account_address, 0x03), 0xb0e95b83a36ce98218879ec55c33085514ff7f00000000000000000000000001)
        self.assertEqual(world.get_storage_data(account_address, 0x04), 0xc482ab56ec19186dc48c88f30861a850b2253b1ea6dc021589e569bd47f400ff)
        self.assertEqual(world.get_storage_data(account_address, 0x05), 0xcf45c7f9af4bbe4a83055b55b97777ad5e0a3f08b129c9ae208c5d713c0c00ff)
        self.assertEqual(world.get_storage_data(account_address, 0x06), 0xa5cbb62a421049b0f000b68fb921f7aa6aff8100000000000000000000000001)
        self.assertEqual(world.get_storage_data(account_address, 0x07), 0x3bde6ca66dffe1bf5d727c3edea74c7a4af43b3912e6256d37705c8f3bf40101)
        self.assertEqual(world.get_storage_data(account_address, 0x08), 0x3f49a1e40c5213aa4ffed57eb4c1ad2d181b2aaa289e9d59c2256c43480c0101)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 863482)

    def test_expPowerOf256Of256_30(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest/expPowerOf256Of256_30.json
            sha256sum: 1f1fac5e60b053bd4dbfe61f194b7055e6b30c5ed87c4129d3017f35814bca59
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
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 1000000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('601e6101000a6101000a600055601e60ff0a6101000a600155601e6101010a6101000a600255601e6101000a60ff0a600355601e60ff0a60ff0a600455601e6101010a60ff0a600555601e6101000a6101010a600655601e60ff0a6101010a600755601e6101010a6101010a600855'))
        #check storage
        self.assertEqual(world.get_storage_data(account_address, 0x03), 0x7f00000000000000000000000000000000000000000000000000000000000001)
        self.assertEqual(world.get_storage_data(account_address, 0x04), 0xe9772778f50fa0a69cd10fa019ac56d72ac7a7d7af26c4ba28415c8f41e200ff)
        self.assertEqual(world.get_storage_data(account_address, 0x05), 0x33f0385ef73feebdb952e5adb643dd0fa178fd9271578219ad50a73d241e00ff)
        self.assertEqual(world.get_storage_data(account_address, 0x06), 0x8100000000000000000000000000000000000000000000000000000000000001)
        self.assertEqual(world.get_storage_data(account_address, 0x07), 0xfd405cce8f73dffc04a6f0ff6ffc6bf7961876d09c5b4933a68f0cc623e20101)
        self.assertEqual(world.get_storage_data(account_address, 0x08), 0xc5a8f4566fd2e96e4ce3a8b3ec0863e7b20bc3b2f3dc5261ba8a0174421e0101)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 861862)

    def test_mod1(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest/mod1.json
            sha256sum: 64ea3bd3cbc9bd60a501fb4fc6c9dda3b110fd6b10e950d8a689e0996ee0c7d3
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
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('60027fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff06600055'))
        #check storage
        self.assertEqual(world.get_storage_data(account_address, 0x00), 0x01)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 79986)

    def test_expPowerOf256Of256_26(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest/expPowerOf256Of256_26.json
            sha256sum: 68c7492ef44fee359f59a9445d28f2286ef4325e970e705135236b2509426e81
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
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 1000000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('601a6101000a6101000a600055601a60ff0a6101000a600155601a6101010a6101000a600255601a6101000a60ff0a600355601a60ff0a60ff0a600455601a6101010a60ff0a600555601a6101000a6101010a600655601a60ff0a6101010a600755601a6101010a6101010a600855'))
        #check storage
        self.assertEqual(world.get_storage_data(account_address, 0x03), 0x085514ff7f000000000000000000000000000000000000000000000000000001)
        self.assertEqual(world.get_storage_data(account_address, 0x04), 0x1d164db738eb6893868b361ad2803f97be35764456e82a837667a693d1e600ff)
        self.assertEqual(world.get_storage_data(account_address, 0x05), 0x8b92c24abebf376a5aab5ff4dfd3538a03d38a10bced2aae8e1a8a85b81a00ff)
        self.assertEqual(world.get_storage_data(account_address, 0x06), 0xf7aa6aff81000000000000000000000000000000000000000000000000000001)
        self.assertEqual(world.get_storage_data(account_address, 0x07), 0x6931bda98c70e860a1f6a5224940f1ec7e6734cd9456c95806384f7cb7e60101)
        self.assertEqual(world.get_storage_data(account_address, 0x08), 0x3402a9db66492dfc2a220715e76243469462f24edc56903ba1d8e96ed21a0101)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 862222)

    def test_expPowerOf256_1(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest/expPowerOf256_1.json
            sha256sum: 5b3094ea3a2240323ee22bcdfa3bf5de0fd98be21f77b4c9ee4e53936a964210
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
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('60016101000a600055600160ff0a60015560016101010a600255'))
        #check storage
        self.assertEqual(world.get_storage_data(account_address, 0x00), 0x0100)
        self.assertEqual(world.get_storage_data(account_address, 0x01), 0xff)
        self.assertEqual(world.get_storage_data(account_address, 0x02), 0x0101)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 39913)

    def test_mod2(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest/mod2.json
            sha256sum: 39166b6eb33acd43b8b4af891bea3fbde11228f14e2040f6d49998947eb6d414
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
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff600006600055'))
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 94986)

    def test_expPowerOf2_4(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest/expPowerOf2_4.json
            sha256sum: 2e682f31857a63b9ca286ef657a5558bc8a125e8cf86bdce5e9f05599a4e2b1d
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
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('600460020a600055600360020a600155600560020a600255'))
        #check storage
        self.assertEqual(world.get_storage_data(account_address, 0x00), 0x10)
        self.assertEqual(world.get_storage_data(account_address, 0x01), 0x08)
        self.assertEqual(world.get_storage_data(account_address, 0x02), 0x20)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 39913)

    def test_expPowerOf256_14(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest/expPowerOf256_14.json
            sha256sum: f00811a305a3133a6eedd1a3bf6e21192de9ead33b6885afc25cf74f63c90efe
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
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('600e6101000a600055600e60ff0a600155600e6101010a600255'))
        #check storage
        self.assertEqual(world.get_storage_data(account_address, 0x00), 0x010000000000000000000000000000)
        self.assertEqual(world.get_storage_data(account_address, 0x01), 0xf25997e139ada3b331e7945af201)
        self.assertEqual(world.get_storage_data(account_address, 0x02), 0x010e5c6ff0ddc873c2d5ea6c5b0e01)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 39913)

    def test_stop(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest/stop.json
            sha256sum: ee5a3f510d764607ff6bad6db27cffd9b8a77404924d85e555a2aa28ba1df173
            Code: STOP
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('00')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('00'))
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 100000)

    def test_sdivByZero2(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest/sdivByZero2.json
            sha256sum: 39b3fdeae1e4d2d6d27063a22f0852953e47ae4b6baf549c29829d0087ad7bfb
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
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('600160007ffffffffffffffffffffffffffffffffffffffffffffffffffffffffcf923bdff6000030501600055'))
        #check storage
        self.assertEqual(world.get_storage_data(account_address, 0x00), 0x01)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 79974)

    def test_sdiv4(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest/sdiv4.json
            sha256sum: 69de65200dc434ceb6be63eecd51eee55c9dba1b586554b99837f07710bc4bfd
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
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('6004600003600505600055'))
        #check storage
        self.assertEqual(world.get_storage_data(account_address, 0x00), 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 79980)

    def test_expPowerOf256_7(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest/expPowerOf256_7.json
            sha256sum: 0abac540c5d55381e27d3cef896271d20bd89886ee6f5e85d5c17796056560fc
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
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('60076101000a600055600760ff0a60015560076101010a600255'))
        #check storage
        self.assertEqual(world.get_storage_data(account_address, 0x00), 0x0100000000000000)
        self.assertEqual(world.get_storage_data(account_address, 0x01), 0xf914dd22eb06ff)
        self.assertEqual(world.get_storage_data(account_address, 0x02), 0x0107152323150701)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 39913)

    def test_add3(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest/add3.json
            sha256sum: 866aaac3bd7d8b66273d8f53bdcf11bed10d4157d091c525304360f211285fbb
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
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('6000600001600055'))
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 94988)

    def test_expPowerOf256_26(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest/expPowerOf256_26.json
            sha256sum: 04f921d2b6e5621f895f69d5beb03ed1e49840de54ff8de1c673a93acee94ab8
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
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('601a6101000a600055601a60ff0a600155601a6101010a600255'))
        #check storage
        self.assertEqual(world.get_storage_data(account_address, 0x00), 0x010000000000000000000000000000000000000000000000000000)
        self.assertEqual(world.get_storage_data(account_address, 0x01), 0xe73b116885641f4651a56f438fd08d61869cfa55465bd944e601)
        self.assertEqual(world.get_storage_data(account_address, 0x02), 0x011b4f636a81778ea1c96f4cab2b998cbc26b00c572e7029451a01)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 39913)

    def test_not1(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest/not1.json
            sha256sum: ff54afc71fd0bec8b8a6032cc79f3e08fdf83d3637eae42db69706846262b3c8
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
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 1000000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('6201e2406000526000511960005260206000f3'))
        #check outs
        self.assertEqual(returndata, unhexlify('fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe1dbf'))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 999967)

    def test_mul0(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest/mul0.json
            sha256sum: a1c0d020e16b600d2132f2458285cc0688bcea7855ac0fc1346778239e09d60a
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
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('6003600202600055'))
        #check storage
        self.assertEqual(world.get_storage_data(account_address, 0x00), 0x06)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 79986)

    def test_addmod1_overflow2(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest/addmod1_overflow2.json
            sha256sum: 1ca4f6d408f2e9f74b629103e89ebba8d9720ce4e3cab4e3349a29b43cf17995
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
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 10000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('60056000600160000308600055'))
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 4974)

    def test_exp6(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest/exp6.json
            sha256sum: be7b3be54ac4595f9c4765478d535bb4be42d284efcf090b7a5115d7123d24b0
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
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('61010160010a600055'))
        #check storage
        self.assertEqual(world.get_storage_data(account_address, 0x00), 0x01)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 79961)

    def test_mul7(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest/mul7.json
            sha256sum: 1d1014053dc219e82ead07af3a96c64d1681b2b74e141dca090d87dd4f766355
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
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('7001234567890abcdef0fedcba09876543217001234567890abcdef0fedcba09876543217001234567890abcdef0fedcba0987654321020260005260206000f3'))
        #check outs
        self.assertEqual(returndata, unhexlify('47d0817e4167b1eb4f9fc722b133ef9d7d9a6fb4c2c1c442d000107a5e419561'))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 99966)

    def test_sdivByZero1(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest/sdivByZero1.json
            sha256sum: 680f7a71f087c03fd46bf81c4a1b97ea0d2c4a1e0d04319b4351da0880235506
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
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('60007fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff60000305600055'))
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 94980)

    def test_signextend_BitIsSetInHigherByte(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest/signextend_BitIsSetInHigherByte.json
            sha256sum: 0fce8f370ba4c2d3654aa00c341b472548d4e0fd8acfe30544186da563871d52
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
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 1000000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('6212faf460010b600055'))
        #check storage
        self.assertEqual(world.get_storage_data(account_address, 0x00), 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffaf4)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 979986)

    def test_addmod2_1(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest/addmod2_1.json
            sha256sum: bec7a5667e42343f21c02993ebf7e246ce3f7673c3597ebb1c4f70ad2d0d37e6
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
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('60036001600660000308600360056000030614600055'))
        #check storage
        self.assertEqual(world.get_storage_data(account_address, 0x00), 0x01)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 79954)

    def test_signextend_BitIsNotSetInHigherByte(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest/signextend_BitIsNotSetInHigherByte.json
            sha256sum: 959b21fdd2ff98f3e295c9e0f5ec59c3e4c34aa052f5f063a66de36e4bb4f1df
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
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 1000000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('62126af460010b600055'))
        #check storage
        self.assertEqual(world.get_storage_data(account_address, 0x00), 0x6af4)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 979986)

    def test_divByNonZero0(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest/divByNonZero0.json
            sha256sum: f4cf683a1b1cb050fca2368a5dc7a77a212cb4ce1a65ddce6da7710d031b3667
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
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('6002600504600055'))
        #check storage
        self.assertEqual(world.get_storage_data(account_address, 0x00), 0x02)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 79986)

    def test_expPowerOf256_10(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest/expPowerOf256_10.json
            sha256sum: f8c9982c1b839231b20b4c4eb6db3da0812bda157777ce3a60f82ba84af244a2
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
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('600a6101000a600055600a60ff0a600155600a6101010a600255'))
        #check storage
        self.assertEqual(world.get_storage_data(account_address, 0x00), 0x0100000000000000000000)
        self.assertEqual(world.get_storage_data(account_address, 0x01), 0xf62c88d104d1882cf601)
        self.assertEqual(world.get_storage_data(account_address, 0x02), 0x010a2d78d2fcd2782d0a01)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 39913)

    def test_add0(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest/add0.json
            sha256sum: 736331695222afa357efb13d6e80e9444b1c1243da1e28b49748f7fc0d4748b6
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
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff01600055'))
        #check storage
        self.assertEqual(world.get_storage_data(account_address, 0x00), 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 79988)

    def test_sdiv9(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest/sdiv9.json
            sha256sum: 5d45e9e2d10bb7da099ab34e4e5e9679a7c4b83c80936f572602bec6270248bc
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
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('6001600160000305600055'))
        #check storage
        self.assertEqual(world.get_storage_data(account_address, 0x00), 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 79980)

    def test_expPowerOf256_11(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest/expPowerOf256_11.json
            sha256sum: 2fd601380898a7b6cb04e50d6c370d4b374da2e93a496a68dce6ba9356057286
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
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('600b6101000a600055600b60ff0a600155600b6101010a600255'))
        #check storage
        self.assertEqual(world.get_storage_data(account_address, 0x00), 0x010000000000000000000000)
        self.assertEqual(world.get_storage_data(account_address, 0x01), 0xf5365c4833ccb6a4c90aff)
        self.assertEqual(world.get_storage_data(account_address, 0x02), 0x010b37a64bcfcf4aa5370b01)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 39913)

    def test_smod2(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest/smod2.json
            sha256sum: 816ae267e8e019ad77267dc991e2cfa7bc6d5283e0df745e21e5f6de1a64c247
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
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('6003600560000307600055'))
        #check storage
        self.assertEqual(world.get_storage_data(account_address, 0x00), 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 79980)

    def test_add4(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest/add4.json
            sha256sum: c11a6ac2534dfd472a0704db2b87fbaa3ca1869053d05398dc1fc562b03c6312
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
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff600101600055'))
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 94988)

    def test_expPowerOf256_24(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest/expPowerOf256_24.json
            sha256sum: bac79e701cef51c594d7fa7841e90b00d53b6949d53870f0d694c3e45d32cb5c
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
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('60186101000a600055601860ff0a60015560186101010a600255'))
        #check storage
        self.assertEqual(world.get_storage_data(account_address, 0x00), 0x01000000000000000000000000000000000000000000000000)
        self.assertEqual(world.get_storage_data(account_address, 0x01), 0xe90c40de00872d19573a8d23493fc3a9151e217a1913e801)
        self.assertEqual(world.get_storage_data(account_address, 0x02), 0x01191c122a1b1745008367f9509126ae39066a3189e9141801)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 39913)

    def test_smod4(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest/smod4.json
            sha256sum: f959fa94acee962550d80b98ab3ad73d9a974299985fa3dfab33bc38dabdb0e6
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
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('6000600260000307600055'))
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 94980)

    def test_expPowerOf256Of256_19(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest/expPowerOf256Of256_19.json
            sha256sum: 62e370e3a991db76e05317783c12da64424932367e6d6d5fabf42ff073e4eb3f
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
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 1000000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('60136101000a6101000a600055601360ff0a6101000a60015560136101010a6101000a60025560136101000a60ff0a600355601360ff0a60ff0a60045560136101010a60ff0a60055560136101000a6101010a600655601360ff0a6101010a60075560136101010a6101010a600855'))
        #check storage
        self.assertEqual(world.get_storage_data(account_address, 0x03), 0x8218879ec55c33085514ff7f0000000000000000000000000000000000000001)
        self.assertEqual(world.get_storage_data(account_address, 0x04), 0xb795ad7ac24cfbb7435cf53bd3584f3d4b2709935635c3ceb66e761ff091feff)
        self.assertEqual(world.get_storage_data(account_address, 0x05), 0x1f0bb7be91a0ccd0cca93d75cf03de3e6b56fe8f1c54242617665327219300ff)
        self.assertEqual(world.get_storage_data(account_address, 0x06), 0xb0f000b68fb921f7aa6aff810000000000000000000000000000000000000001)
        self.assertEqual(world.get_storage_data(account_address, 0x07), 0xad571756ecbff1bfdef064861e5e92c5d897a9cc380e54bdbaabd80bb793ff01)
        self.assertEqual(world.get_storage_data(account_address, 0x08), 0xd8b5b531989e689f700dcdb43ab90e79a49dfbbb5a13dbf751df98bb34930101)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 862852)

    def test_addmod2(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest/addmod2.json
            sha256sum: bc3fff0b3f891b0c94144c3c1826111c02c54083edc3a2e844d830dd5c1c3c50
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
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('60036001600660000308600055'))
        #check storage
        self.assertEqual(world.get_storage_data(account_address, 0x00), 0x02)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 79974)

    def test_signextend_00(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest/signextend_00.json
            sha256sum: 730da386317e267b2357bcd8de8ca17af8a23fe36b6ad63810ffb306f111b6c3
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
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 1000000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('600060000b600055'))
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 994986)

    def test_expPowerOf256_3(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest/expPowerOf256_3.json
            sha256sum: 56b02cf353609f247c1b4223a10cd562909fa54a624d5f343297f3e1bd457134
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
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('60036101000a600055600360ff0a60015560036101010a600255'))
        #check storage
        self.assertEqual(world.get_storage_data(account_address, 0x00), 0x01000000)
        self.assertEqual(world.get_storage_data(account_address, 0x01), 0xfd02ff)
        self.assertEqual(world.get_storage_data(account_address, 0x02), 0x01030301)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 39913)

    def test_addmod3_0(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest/addmod3_0.json
            sha256sum: c3c177cfc1f4f72c05a2bae7e70907f35fbbb7bb4d4a347ac476ddc5efe44445
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
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('60026003600003600160040814600055'))
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 94968)

    def test_signextend_Overflow_dj42(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest/signextend_Overflow_dj42.json
            sha256sum: be60f2b5a150a75aca6a8f6f392df92fdf89e819b4c63a7f225f6bf8c5801367
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
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 1000000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('6005565b005b61800080680100000000000000010b6180011160035763badf000d601155'))
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 999954)

    def test_mulmod3_0(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest/mulmod3_0.json
            sha256sum: 8e0cfb3d6d85f04d16d0303caa1f6ebfb9e6d8a45385fb2019ff1ee247d6aab9
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
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('60026003600003600160050914600055'))
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 94968)

    def test_expPowerOf2_2(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest/expPowerOf2_2.json
            sha256sum: dfae7ac1edf0e37b30fe2fa536a1b4f466f91750be493286a62adf8cbd920a25
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
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('600260020a600055600160020a600155600360020a600255'))
        #check storage
        self.assertEqual(world.get_storage_data(account_address, 0x00), 0x04)
        self.assertEqual(world.get_storage_data(account_address, 0x01), 0x02)
        self.assertEqual(world.get_storage_data(account_address, 0x02), 0x08)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 39913)

    def test_arith1(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest/arith1.json
            sha256sum: 4de94cede543038ac262106c0fdfd4aa18e8f8e5620b0549582659d2c63865e0
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
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 1000000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('6001600190016007026005016002900460049060016021900560150160030260059007600303600960110a60005260086000f3'))
        #check outs
        self.assertEqual(returndata, unhexlify('0000000000000000'))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 999871)

    def test_sub3(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest/sub3.json
            sha256sum: 64aa42730370eeff5533f56898060b68d71278371d7ff432ae056cb4bd054b07
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
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff600003600055'))
        #check storage
        self.assertEqual(world.get_storage_data(account_address, 0x00), 0x01)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 79988)

    def test_signextendInvalidByteNumber(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest/signextendInvalidByteNumber.json
            sha256sum: 425f9c6e5875fc4df3b9dce9bf13dfd40689b848614446d5e7c9193b012060d8
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
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 1000000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('62126af460500b600055'))
        #check storage
        self.assertEqual(world.get_storage_data(account_address, 0x00), 0x126af4)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 979986)

    def test_mulmod1(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest/mulmod1.json
            sha256sum: c8bff028b610b8868f5e4677c57c7ab603183ae0995fbcca52c9cfbcf173d042
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
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('60036002600003600160000309600055'))
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 94968)

    def test_mulmod1_overflow4(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest/mulmod1_overflow4.json
            sha256sum: fdbf6eb43ab05ba46d9fe3ec78d9adf052782480dff781b7009bb139bdaa2768
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
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 1000000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('600560027f800000000000000000000000000000000000000000000000000000000000000109600055'))
        #check storage
        self.assertEqual(world.get_storage_data(account_address, 0x00), 0x03)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 979980)

    def test_expPowerOf256Of256_9(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest/expPowerOf256Of256_9.json
            sha256sum: 5579a595d61dd3260cd161086c9f14d8a11389a2042efabb9b7f12d8889d9c8d
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
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 1000000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('60096101000a6101000a600055600960ff0a6101000a60015560096101010a6101000a60025560096101000a60ff0a600355600960ff0a60ff0a60045560096101010a60ff0a60055560096101000a6101010a600655600960ff0a6101010a60075560096101010a6101010a600855'))
        #check storage
        self.assertEqual(world.get_storage_data(account_address, 0x03), 0x53017d8eb210db2c8cd4a299079ec55c33085514ff7f00000000000000000001)
        self.assertEqual(world.get_storage_data(account_address, 0x04), 0x48be09b6c6ae2aa660f1972125cecbb1038b5d236ecf766ba786e2c4e887feff)
        self.assertEqual(world.get_storage_data(account_address, 0x05), 0x2e350d847ba73dc2099f83f532951c47269d9fd7e411b50bae00a9581f8900ff)
        self.assertEqual(world.get_storage_data(account_address, 0x06), 0x013ab9e1f0df89a184b4d07080b68fb921f7aa6aff8100000000000000000001)
        self.assertEqual(world.get_storage_data(account_address, 0x07), 0xf387ed41c1050f9da667f429a3e8fb30b61a55ede97d7b8acd797a03cd89ff01)
        self.assertEqual(world.get_storage_data(account_address, 0x08), 0x525696c22bb3ce00fd2e3f6bbb9b4ea1046a5e31fcff2fedf8f8c74d28890101)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 863752)

    def test_exp3(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest/exp3.json
            sha256sum: 9e1807553a85e97e932a157ecc6d53baaf5d5ee1557e853ffc757ba252f35396
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
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('637fffffff60000a600055'))
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 94941)

    def test_sub2(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest/sub2.json
            sha256sum: 7de89ad08fca16c010007c4d071bb65fa53c7ac93cf59af41f5b305196068328
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
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('6017600003600055'))
        #check storage
        self.assertEqual(world.get_storage_data(account_address, 0x00), 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe9)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 79988)

    def test_signextend_bigBytePlus1(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest/signextend_bigBytePlus1.json
            sha256sum: b3dbaf26abc5c657d7cbe8741bd09690af724a6b4d6d6062864dc355f4af8611
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
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 1000000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('66f000000000000161ffff0b600055'))
        #check storage
        self.assertEqual(world.get_storage_data(account_address, 0x00), 0xf0000000000001)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 979986)

    def test_expPowerOf256_15(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest/expPowerOf256_15.json
            sha256sum: 6715731187f2daeec8f28a29e349efe023d659c1422d40dee0236b2e978de8a2
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
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('600f6101000a600055600f60ff0a600155600f6101010a600255'))
        #check storage
        self.assertEqual(world.get_storage_data(account_address, 0x00), 0x01000000000000000000000000000000)
        self.assertEqual(world.get_storage_data(account_address, 0x01), 0xf1673e495873f60f7eb5acc6970eff)
        self.assertEqual(world.get_storage_data(account_address, 0x02), 0x010f6acc60cea63c3698c056c7690f01)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 39913)

    def test_addmod1_overflow4(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest/addmod1_overflow4.json
            sha256sum: d662a17e9b400a5a68db047b8a36126693aeef69d322bebc5fde04347fbcfbfb
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
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 1000000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('60056002600160000308600055'))
        #check storage
        self.assertEqual(world.get_storage_data(account_address, 0x00), 0x02)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 979974)

    def test_sub4(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest/sub4.json
            sha256sum: b37741b2c3ae3fcd372612630d8678ea68d3c88d76742b2c41c9a890700a0990
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
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('60007fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff03600055'))
        #check storage
        self.assertEqual(world.get_storage_data(account_address, 0x00), 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 79988)

    def test_expPowerOf256_4(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest/expPowerOf256_4.json
            sha256sum: 7ebf96497b90ecacabd4a4341d29c4e246e9ac21dfc9f23a192177dbb9816d60
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
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('60046101000a600055600460ff0a60015560046101010a600255'))
        #check storage
        self.assertEqual(world.get_storage_data(account_address, 0x00), 0x0100000000)
        self.assertEqual(world.get_storage_data(account_address, 0x01), 0xfc05fc01)
        self.assertEqual(world.get_storage_data(account_address, 0x02), 0x0104060401)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 39913)

    def test_expPowerOf256_30(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest/expPowerOf256_30.json
            sha256sum: 37bec030ecb1c60ffc208c8c5d08f472d6a6aef8952edc5c5028bcb7e6ba5032
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
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('601e6101000a600055601e60ff0a600155601e6101010a600255'))
        #check storage
        self.assertEqual(world.get_storage_data(account_address, 0x00), 0x01000000000000000000000000000000000000000000000000000000000000)
        self.assertEqual(world.get_storage_data(account_address, 0x01), 0xe3a38ce946b71e74e8ebc966d90f0b139e66b560e1f5b542c0fd25b2e201)
        self.assertEqual(world.get_storage_data(account_address, 0x02), 0x011fc34942d8d9831a0811d8412aecf1e1f58031ffbc16699c151cddb31e01)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 39913)

    def test_mul4(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest/mul4.json
            sha256sum: 34bf5a1ec40d9dca4bfff8b1109e2f16747f472a880b6eaec0718e44397f8afb
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
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7f800000000000000000000000000000000000000000000000000000000000000002600055'))
        #check storage
        self.assertEqual(world.get_storage_data(account_address, 0x00), 0x8000000000000000000000000000000000000000000000000000000000000000)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 79986)

    def test_sdiv8(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest/sdiv8.json
            sha256sum: a8e645293f2eaba2ddb5b2fc53ff1fe057e77b2726d26401ab3414a5b1229c3b
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
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('6001600003600160000305600055'))
        #check storage
        self.assertEqual(world.get_storage_data(account_address, 0x00), 0x01)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 79974)

    def test_addmodDivByZero2(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest/addmodDivByZero2.json
            sha256sum: 36f7f7fe308f7c655d9e676dd20a7712f4600daaf07299750f0b6a432bf08989
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
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('60006000600108600055'))
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 94980)

    def test_expPowerOf256Of256_8(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmArithmeticTest/expPowerOf256Of256_8.json
            sha256sum: b006d7d89163145118798640973cf35f8f80c623b5c73f6ce553cf3bc735842a
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
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f2947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 10000000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('60086101000a6101000a600055600860ff0a6101000a60015560086101010a6101000a60025560086101000a60ff0a600355600860ff0a60ff0a60045560086101010a60ff0a60055560086101000a6101010a600655600860ff0a6101010a60075560086101010a6101010a600855'))
        #check storage
        self.assertEqual(world.get_storage_data(account_address, 0x03), 0x230041a0e7602d6e459609ed39081ec55c33085514ff7f000000000000000001)
        self.assertEqual(world.get_storage_data(account_address, 0x04), 0xc407d8a413ef9079ead457ed686a05ac81039c0cae0a7f6afd01e8461ff800ff)
        self.assertEqual(world.get_storage_data(account_address, 0x05), 0x67a397e0692385e4cd83853aabce220a94d449e885fa867e96d3ef5e180800ff)
        self.assertEqual(world.get_storage_data(account_address, 0x06), 0x70add926e753655d6d0ebe9c0f81368fb921f7aa6aff81000000000000000001)
        self.assertEqual(world.get_storage_data(account_address, 0x07), 0x0bdce80b8378e43f13d454b9d0a4c83cf311b8eaa45d5122cfd544a217f80101)
        self.assertEqual(world.get_storage_data(account_address, 0x08), 0x629c25790e1488998877a9ecdf0fb69637e77d8a4bdc1b46270093ba20080101)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 9863842)

if __name__ == '__main__':
    unittest.main()
