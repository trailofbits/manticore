
#Taken from /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmEnvironmentalInfo
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

class EVMTest_vmEnvironmentalInfo(unittest.TestCase):
    _multiprocess_can_split_ = True
    maxDiff=None 


    def test_calldatacopy2_return(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmEnvironmentalInfo/calldatacopy2_return.json
            sha256sum: 72d0ee7ce7847b92419899064e0809ef7670640a67908acc7fef80d32910129a
            Code: PUSH1 0x0
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
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('60006001600037600051600055596000f3')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x3b9aca00
        data = unhexlify('1234567890abcdef01234567890abcdef0')
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('60006001600037600051600055596000f3'))
        #check outs
        self.assertEqual(returndata, unhexlify('0000000000000000000000000000000000000000000000000000000000000000'))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 99999994971)

    def test_calldatacopy1_return(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmEnvironmentalInfo/calldatacopy1_return.json
            sha256sum: e172b86326fa5b9be1f8e0c19c52f846d323121428f59f5555e857896961e81f
            Code: PUSH1 0x1
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
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('60016001600037600051600055596000f3')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x3b9aca00
        data = unhexlify('1234567890abcdef01234567890abcdef0')
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('60016001600037600051600055596000f3'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0x3400000000000000000000000000000000000000000000000000000000000000)
        #check outs
        self.assertEqual(returndata, unhexlify('3400000000000000000000000000000000000000000000000000000000000000'))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 99999979968)

    def test_calldatacopy0_return(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmEnvironmentalInfo/calldatacopy0_return.json
            sha256sum: cb48c4b420c6c35731a769cd72b2d2d9a1f25d32bfc15e18cc26ba088a3cfad2
            Code: PUSH1 0x2
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
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('60026001600037600051600055596000f3')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x3b9aca00
        data = unhexlify('1234567890abcdef01234567890abcdef0')
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('60026001600037600051600055596000f3'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0x3456000000000000000000000000000000000000000000000000000000000000)
        #check outs
        self.assertEqual(returndata, unhexlify('3456000000000000000000000000000000000000000000000000000000000000'))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 99999979968)

    def test_calldatacopy0(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmEnvironmentalInfo/calldatacopy0.json
            sha256sum: 0d8008f844fb6c7bbd27cdfd47322add5f4970eb909aa997774c9c4e3f75533c
            Code: PUSH1 0x2
                  PUSH1 0x1
                  PUSH1 0x0
                  CALLDATACOPY
                  PUSH1 0x0
                  MLOAD
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('60026001600037600051600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=100000000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x3b9aca00
        data = unhexlify('1234567890abcdef01234567890abcdef0')
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
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('60026001600037600051600055'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0x3456000000000000000000000000000000000000000000000000000000000000)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 99999979973)

    def test_calldataload1(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmEnvironmentalInfo/calldataload1.json
            sha256sum: f4ef49578253c7549cabf4ba3ebf56f9d4ae9814d741370431d9fe5a7b54b512
            Code: PUSH1 0x1
                  CALLDATALOAD
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('600135600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=100000000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x3b9aca00
        data = unhexlify('ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff23')
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
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('600135600055'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff23)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 99999979991)

    def test_calldatacopy_DataIndexTooHigh2_return(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmEnvironmentalInfo/calldatacopy_DataIndexTooHigh2_return.json
            sha256sum: 1d7ad9ef5326d7ae2b519b2c357ca936687f08415b0e9cac9071475de6072256
            Code: PUSH1 0x9
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
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('60097ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffa600037600051600055596000f3')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x3b9aca00
        data = unhexlify('1234567890abcdef01234567890abcdef0')
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('60097ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffa600037600051600055596000f3'))
        #check outs
        self.assertEqual(returndata, unhexlify('0000000000000000000000000000000000000000000000000000000000000000'))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 99999994968)

    def test_calldatacopy_sec(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmEnvironmentalInfo/calldatacopy_sec.json
            sha256sum: efedf891fed919f137379f30d45b6205361a2ea6a42b6a9a9963f6a9a50cacf8
            Code: PUSH1 0x5
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
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('6005565b005b6042601f536101036000601f3760005180606014600357640badc0ffee60ff55')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x3b9aca00
        data = unhexlify('1234567890abcdef01234567890abcdef0')
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('6005565b005b6042601f536101036000601f3760005180606014600357640badc0ffee60ff55'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0xff)), 0x0badc0ffee)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 99999979876)

    def test_calldatacopy2(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmEnvironmentalInfo/calldatacopy2.json
            sha256sum: 1833277abb6243a419dee2edf8a7dd737f39cf2e75d4af18d43e220fd94ffa6d
            Code: PUSH1 0x0
                  PUSH1 0x1
                  PUSH1 0x0
                  CALLDATACOPY
                  PUSH1 0x0
                  MLOAD
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('60006001600037600051600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=100000000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x3b9aca00
        data = unhexlify('1234567890abcdef01234567890abcdef0')
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
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('60006001600037600051600055'))
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 99999994976)

    def test_codesize(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmEnvironmentalInfo/codesize.json
            sha256sum: 73114af0ad02b9daba3e2fb62385ce126d0cfa7a970924a4ac18ac133a3629d0
            Code: CODESIZE
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('38600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=100000000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x3b9aca00
        data = unhexlify('1234567890abcdef01234567890abcdef0')
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
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('38600055'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0x04)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 99999979995)

    def test_calldataloadSizeTooHighPartial(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmEnvironmentalInfo/calldataloadSizeTooHighPartial.json
            sha256sum: 9bae33d267b4bc6056a07bc7f2e79582b8b391f812b4d4179b6ffe1c2000e50d
            Code: PUSH1 0xa
                  CALLDATALOAD
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('600a35600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=100000000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x3b9aca00
        data = unhexlify('123456789abcdef00000000000000000000000000000000000000000000024')
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
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('600a35600055'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0x240000000000000000000000)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 99999979991)

    def test_calldataload2(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmEnvironmentalInfo/calldataload2.json
            sha256sum: 740a181d6300bb2f3b40cbde072c9d659dbc485f929ec1fb43f89d21060f8fb0
            Code: PUSH1 0x5
                  CALLDATALOAD
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('600535600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=100000000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x3b9aca00
        data = unhexlify('123456789abcdef00000000000000000000000000000000000000000000000000024')
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
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('600535600055'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0xbcdef00000000000000000000000000000000000000000000000000024000000)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 99999979991)

    def test_calldatacopyUnderFlow(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmEnvironmentalInfo/calldatacopyUnderFlow.json
            sha256sum: 2b8bb4ba697a0e61343ac76bc011d30292c89ed3d099a29ed1c6f1e23af7c42e
            Code: PUSH1 0x1
                  PUSH1 0x2
                  CALLDATACOPY
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('6001600237')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=100000000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x3b9aca00
        data = unhexlify('1234567890abcdef01234567890abcdef0')
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
        #If test end in exception ceck it here
        self.assertTrue(result in ('THROW'))

    def test_calldatacopyZeroMemExpansion_return(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmEnvironmentalInfo/calldatacopyZeroMemExpansion_return.json
            sha256sum: 1c1aaba2a5f840a816ee0a06c82fe54779ffa2161bae2e505ea506567f50c41b
            Code: PUSH1 0x0
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
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('60006000600037600051600055596000f3')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x3b9aca00
        data = unhexlify('1234567890abcdef01234567890abcdef0')
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('60006000600037600051600055596000f3'))
        #check outs
        self.assertEqual(returndata, unhexlify('0000000000000000000000000000000000000000000000000000000000000000'))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 99999994971)

    def test_calldatacopy_DataIndexTooHigh(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmEnvironmentalInfo/calldatacopy_DataIndexTooHigh.json
            sha256sum: f5e9ecfae9eec929d509ceaf0babb5c0938fd6fe129865d38d5e1b4a8490aee6
            Code: PUSH1 0xff
                  PUSH32 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffa
                  PUSH1 0x0
                  CALLDATACOPY
                  PUSH1 0x0
                  MLOAD
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('60ff7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffa600037600051600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=100000000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x3b9aca00
        data = unhexlify('1234567890abcdef01234567890abcdef0')
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
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('60ff7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffa600037600051600055'))
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 99999994931)

    def test_origin(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmEnvironmentalInfo/origin.json
            sha256sum: 02941d61ed42efefb2a75e4313b67bf27279c297c02b821840be18d088a60fbe
            Code: ORIGIN
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('32600055')
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
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('32600055'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0xcd1722f3947def4cf144679da39c4c32bdc35681)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 99999979995)

    def test_codecopy0(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmEnvironmentalInfo/codecopy0.json
            sha256sum: 87db1ebad34535c717092ae7e8afa414a7116e8118b91cd289457ded6d6ca49b
            Code: PUSH1 0x5
                  PUSH1 0x0
                  PUSH1 0x0
                  CODECOPY
                  PUSH1 0x0
                  MLOAD
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('60056000600039600051600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=100000000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x3b9aca00
        data = unhexlify('1234567890abcdef01234567890abcdef0')
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
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('60056000600039600051600055'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0x6005600060000000000000000000000000000000000000000000000000000000)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 99999979973)

    def test_codecopyZeroMemExpansion(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmEnvironmentalInfo/codecopyZeroMemExpansion.json
            sha256sum: e7dd5f8b867a9cd4c8066f05592c70093c96954e3982e9823823c02e37a75e53
            Code: PUSH1 0x0
                  PUSH1 0x0
                  PUSH1 0x0
                  CODECOPY
                  PUSH1 0x0
                  MLOAD
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('60006000600039600051600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=100000000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x3b9aca00
        data = unhexlify('1234567890abcdef01234567890abcdef0')
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
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('60006000600039600051600055'))
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 99999994976)

    def test_calldatacopy_DataIndexTooHigh2(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmEnvironmentalInfo/calldatacopy_DataIndexTooHigh2.json
            sha256sum: d7c437182aa3904609ab52df4f709a1fcef36dd5b690d59ac9ea64585837dd6c
            Code: PUSH1 0x9
                  PUSH32 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffa
                  PUSH1 0x0
                  CALLDATACOPY
                  PUSH1 0x0
                  MLOAD
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('60097ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffa600037600051600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=100000000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x3b9aca00
        data = unhexlify('1234567890abcdef01234567890abcdef0')
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
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('60097ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffa600037600051600055'))
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 99999994973)

    def test_calldatasize1(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmEnvironmentalInfo/calldatasize1.json
            sha256sum: 044142d13d4c68724d1a266ecb09e9cf2404dda16f48cb66f7f6a1f09fe9ecfc
            Code: CALLDATASIZE
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('36600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=100000000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x3b9aca00
        data = unhexlify('ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff23')
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
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('36600055'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0x21)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 99999979995)

    def test_codecopy_DataIndexTooHigh(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmEnvironmentalInfo/codecopy_DataIndexTooHigh.json
            sha256sum: fabb321754898a481b409635bdc60d7c14bef75ca8bee4ef746eab446e470db5
            Code: PUSH1 0x8
                  PUSH32 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffa
                  PUSH1 0x0
                  CODECOPY
                  PUSH1 0x0
                  MLOAD
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('60087ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffa600039600051600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=100000000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x3b9aca00
        data = unhexlify('1234567890abcdef01234567890abcdef0')
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
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('60087ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffa600039600051600055'))
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 99999994973)

    def test_calldatasize2(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmEnvironmentalInfo/calldatasize2.json
            sha256sum: 604a212fca91e8ffd85b3a50669c468e65c5b8a453cb95099c16bd8493d26f78
            Code: CALLDATASIZE
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('36600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=100000000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x3b9aca00
        data = unhexlify('230000000000000000000000000000000000000000000000000000000000000023')
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
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('36600055'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0x21)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 99999979995)

    def test_calldataloadSizeTooHigh(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmEnvironmentalInfo/calldataloadSizeTooHigh.json
            sha256sum: bee471de3efe5033e5bfb0ad3e1314609dee30ce41894b168e702705a865ebe8
            Code: PUSH32 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffa
                  CALLDATALOAD
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffa35600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=100000000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x3b9aca00
        data = unhexlify('123456789abcdef00000000000000000000000000000000000000000000000000024')
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
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffa35600055'))
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 99999994991)

    def test_address1(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmEnvironmentalInfo/address1.json
            sha256sum: 3c3533457fdd741eff1b246614d8640aaf39ebc1617c77e9e8df1627e4e40b77
            Code: ADDRESS
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('30600055')
        world.create_account(address=0xcd1722f3947def4cf144679da39c4c32bdc35681,
                             balance=100000000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xcd1722f3947def4cf144679da39c4c32bdc35681
        price = 0x3b9aca00
        data = ''
        caller = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
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
        #Add pos checks for account 0xcd1722f3947def4cf144679da39c4c32bdc35681
        #check nonce, balance, code
        self.assertEqual(world.get_nonce(0xcd1722f3947def4cf144679da39c4c32bdc35681), 0)
        self.assertEqual(to_constant(world.get_balance(0xcd1722f3947def4cf144679da39c4c32bdc35681)), 100000000000000000000000)
        self.assertEqual(world.get_code(0xcd1722f3947def4cf144679da39c4c32bdc35681), unhexlify('30600055'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xcd1722f3947def4cf144679da39c4c32bdc35681, 0x00)), 0xcd1722f3947def4cf144679da39c4c32bdc35681)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 99999979995)

    def test_gasprice(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmEnvironmentalInfo/gasprice.json
            sha256sum: 261564b4ca0927cfb1684b5ec3ddca95cf37bdce78b3ed4dda5333e70290913b
            Code: GASPRICE
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('3a600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=100000000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x75bcd15
        data = unhexlify('1234567890abcdef01234567890abcdef0')
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
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('3a600055'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0x075bcd15)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 99999979995)

    def test_callvalue(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmEnvironmentalInfo/callvalue.json
            sha256sum: 4d016151faa4abb689531d874672699f38436935ea205e0beec613bba6d1e896
            Code: CALLVALUE
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('34600055')
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
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('34600055'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0x0de0b6b3a7640000)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 99999979995)

    def test_calldataload_BigOffset(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmEnvironmentalInfo/calldataload_BigOffset.json
            sha256sum: e31c4bcf779c7e8cdef3d5b51742f7365dbb7fd24d3a80660ae215286b1fe9ae
            Code: PUSH32 0x4200000000000000000000000000000000000000000000000000000000000000
                  CALLDATALOAD
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('7f420000000000000000000000000000000000000000000000000000000000000035600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=100000000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x3b9aca00
        data = unhexlify('4200000000000000000000000000000000000000000000000000000000000000')
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
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('7f420000000000000000000000000000000000000000000000000000000000000035600055'))
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 99999994991)

    def test_calldataload0(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmEnvironmentalInfo/calldataload0.json
            sha256sum: d2f771208c138d5c6c6ed53132da0b20eeb954a8190ad7afcdade863aeba0f01
            Code: PUSH1 0x0
                  CALLDATALOAD
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('600035600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=100000000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x3b9aca00
        data = unhexlify('2560')
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
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('600035600055'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0x2560000000000000000000000000000000000000000000000000000000000000)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 99999979991)

    def test_address0(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmEnvironmentalInfo/address0.json
            sha256sum: 69bd89e10c31a23ba45e73a84131bc3c55f283482de6313342dc99acf5a67fea
            Code: ADDRESS
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('30600055')
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
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('30600055'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0x0f572e5295c57f15886f9b263e2f6d2d6c7b5ec6)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 99999979995)

    def test_calldatacopy1(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmEnvironmentalInfo/calldatacopy1.json
            sha256sum: 2155b282d9b9d965fd3d4abc7a1a8ced6b616ac9c4569d9b04ce80c1ae5a2923
            Code: PUSH1 0x1
                  PUSH1 0x1
                  PUSH1 0x0
                  CALLDATACOPY
                  PUSH1 0x0
                  MLOAD
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('60016001600037600051600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=100000000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x3b9aca00
        data = unhexlify('1234567890abcdef01234567890abcdef0')
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
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('60016001600037600051600055'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0x3400000000000000000000000000000000000000000000000000000000000000)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 99999979973)

    def test_calldatacopyZeroMemExpansion(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmEnvironmentalInfo/calldatacopyZeroMemExpansion.json
            sha256sum: ad08c31c88d574670e1132ab5c9fb97b7223b1b5ff7b33e922156e28ab4f5278
            Code: PUSH1 0x0
                  PUSH1 0x0
                  PUSH1 0x0
                  CALLDATACOPY
                  PUSH1 0x0
                  MLOAD
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('60006000600037600051600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=100000000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x3b9aca00
        data = unhexlify('1234567890abcdef01234567890abcdef0')
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
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('60006000600037600051600055'))
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 99999994976)

    def test_calldatasize0(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmEnvironmentalInfo/calldatasize0.json
            sha256sum: 51e6ca6303d754c51e246adebf42e641bb08fdcb6a4636cb34f8426b97e3ad01
            Code: CALLDATASIZE
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('36600055')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=100000000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x3b9aca00
        data = unhexlify('2560')
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
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('36600055'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0x02)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 99999979995)

    def test_calldatacopy_DataIndexTooHigh_return(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmEnvironmentalInfo/calldatacopy_DataIndexTooHigh_return.json
            sha256sum: 9f51012aa4eb821ac5b3402d7369b87806ada5ec8bb9fdee2c4cf48ee558229d
            Code: PUSH1 0xff
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
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('60ff7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffa600037600051600055596000f3')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x3b9aca00
        data = unhexlify('1234567890abcdef01234567890abcdef0')
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
        self.assertEqual(to_constant(world.get_balance(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6)), 1000000000000000000)
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('60ff7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffa600037600051600055596000f3'))
        #check outs
        self.assertEqual(returndata, unhexlify('00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000'))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 99999994926)

    def test_caller(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmEnvironmentalInfo/caller.json
            sha256sum: f254b46de3ddd98140011747a41564be9f4d4c77e669d0a92e5e7db9d0e7ea60
            Code: CALLER
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('33600055')
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
        self.assertEqual(world.get_code(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('33600055'))
        #check storage
        self.assertEqual(to_constant(world.get_storage_data(0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x00)), 0xcd1722f3947def4cf144679da39c4c32bdc35681)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(world.current_vm.gas, 99999979995)

if __name__ == '__main__':
    unittest.main()
