
#Taken from /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmSystemOperations
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

class EVMTest_vmSystemOperations(unittest.TestCase):
    _multiprocess_can_split_ = True
    maxDiff=None 


    def test_return1(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmSystemOperations/return1.json
            sha256sum: 2f407fd89104ac24488eda1e106f34c13033e62b3b0622e38acadfb47ac6755e
            Code: PUSH1 0x37
                  PUSH1 0x0
                  MSTORE8
                  PUSH1 0x0
                  MLOAD
                  PUSH1 0x0
                  SSTORE
                  PUSH1 0x2
                  PUSH1 0x0
                  RETURN
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=10000000)
    
        bytecode = unhexlify('603760005360005160005560026000f3')
        world.create_account(address=0xcd1722f3947def4cf144679da39c4c32bdc35681,
                             balance=23,
                             code=bytecode,
                            )
        address = 0xcd1722f3947def4cf144679da39c4c32bdc35681
        price = 0x5af3107a4000
        data = unhexlify('aa')
        caller = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        value = 23
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
        account_address = 0xcd1722f3947def4cf144679da39c4c32bdc35681
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 23)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('603760005360005160005560026000f3'))
        #check storage
        self.assertEqual(world.get_storage_data(account_address, 0x00), 0x3700000000000000000000000000000000000000000000000000000000000000)
        #check outs
        self.assertEqual(returndata, unhexlify('3700'))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 79973)

    def test_return2(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmSystemOperations/return2.json
            sha256sum: aee3592499031aa92c1580fcec131dd41c42775d7cf782d1ac93e73e48be59b2
            Code: PUSH1 0x37
                  PUSH1 0x0
                  MSTORE8
                  PUSH1 0x0
                  MLOAD
                  PUSH1 0x0
                  SSTORE
                  PUSH1 0x21
                  PUSH1 0x0
                  RETURN
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=10000000)
    
        bytecode = unhexlify('603760005360005160005560216000f3')
        world.create_account(address=0xcd1722f3947def4cf144679da39c4c32bdc35681,
                             balance=23,
                             code=bytecode,
                            )
        address = 0xcd1722f3947def4cf144679da39c4c32bdc35681
        price = 0x5af3107a4000
        data = unhexlify('aa')
        caller = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        value = 23
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
        account_address = 0xcd1722f3947def4cf144679da39c4c32bdc35681
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 23)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('603760005360005160005560216000f3'))
        #check storage
        self.assertEqual(world.get_storage_data(account_address, 0x00), 0x3700000000000000000000000000000000000000000000000000000000000000)
        #check outs
        self.assertEqual(returndata, unhexlify('370000000000000000000000000000000000000000000000000000000000000000'))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 79970)

    def test_suicideNotExistingAccount(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmSystemOperations/suicideNotExistingAccount.json
            sha256sum: 6b2c0fc15dfd8b6ea1595bb658b94b953040da256536e0bcf363fb683f55339a
            Code: PUSH20 0xaa1722f3947def4cf144679da39c4c32bdc35681
                  SELFDESTRUCT
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=10000000)
    
        bytecode = unhexlify('73aa1722f3947def4cf144679da39c4c32bdc35681ff')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=100000000000000000000000,
                             code=bytecode,
                            )
        bytecode = unhexlify('6000355415600957005b60203560003555')
        world.create_account(address=0xcd1722f3947def4cf144679da39c4c32bdc35681,
                             balance=23,
                             code=bytecode,
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f3947def4cf144679da39c4c32bdc35681
        value = 100000
        gas = 1000

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
        account_address = 0xaa1722f3947def4cf144679da39c4c32bdc35681
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 100000000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify(''))
        #Add pos checks for account hex(account_address)
        account_address = 0xcd1722f3947def4cf144679da39c4c32bdc35681
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 23)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('6000355415600957005b60203560003555'))
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 997)

    def test_TestNameRegistrator(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmSystemOperations/TestNameRegistrator.json
            sha256sum: c2f3225283984e12b2ff812d1e8bcd88c7b1fd42fb91fa6de0cbb4eb6dc9c68e
            Code: PUSH1 0x0
                  CALLDATALOAD
                  SLOAD
                  ISZERO
                  PUSH1 0x9
                  JUMPI
                  STOP
                  JUMPDEST
                  PUSH1 0x20
                  CALLDATALOAD
                  PUSH1 0x0
                  CALLDATALOAD
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('6000355415600957005b60203560003555')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=100000000000000000000000,
                             code=bytecode,
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = unhexlify('fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffafffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffa')
        caller = 0xcd1722f3947def4cf144679da39c4c32bdc35681
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
        self.assertEqual(world.get_balance(account_address), 100000000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('6000355415600957005b60203560003555'))
        #check storage
        self.assertEqual(world.get_storage_data(account_address, 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffa), 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffa)
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 79915)

    def test_suicide0(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmSystemOperations/suicide0.json
            sha256sum: d0072d0631c931a683d26954e93d7f3aed1d31591245a4e2f8e717f9e70f53c1
            Code: CALLER
                  SELFDESTRUCT
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=10000000)
    
        bytecode = unhexlify('33ff')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=100000000000000000000000,
                             code=bytecode,
                            )
        bytecode = unhexlify('6000355415600957005b60203560003555')
        world.create_account(address=0xcd1722f3947def4cf144679da39c4c32bdc35681,
                             balance=23,
                             code=bytecode,
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f3947def4cf144679da39c4c32bdc35681
        value = 100000
        gas = 1000

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
        account_address = 0xcd1722f3947def4cf144679da39c4c32bdc35681
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 100000000000000000000023)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('6000355415600957005b60203560003555'))
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 998)

    def test_suicideSendEtherToMe(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmSystemOperations/suicideSendEtherToMe.json
            sha256sum: aa08394a3244b0ddb0844f21f15b94c72a16edbb7f2f136487be7320d268e148
            Code: ADDRESS
                  SELFDESTRUCT
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=10000000)
    
        bytecode = unhexlify('30ff')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=100000000000000000000000,
                             code=bytecode,
                            )
        bytecode = unhexlify('6000355415600957005b60203560003555')
        world.create_account(address=0xcd1722f3947def4cf144679da39c4c32bdc35681,
                             balance=23,
                             code=bytecode,
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f3947def4cf144679da39c4c32bdc35681
        value = 100000
        gas = 1000

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
        account_address = 0xcd1722f3947def4cf144679da39c4c32bdc35681
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 23)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('6000355415600957005b60203560003555'))
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 998)

    def test_return0(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmSystemOperations/return0.json
            sha256sum: c1a73dc918c189133a900125b0c8c6b3e78c699f68f4a8f042fe478d8d731541
            Code: PUSH1 0x37
                  PUSH1 0x0
                  MSTORE8
                  PUSH1 0x0
                  MLOAD
                  PUSH1 0x0
                  SSTORE
                  PUSH1 0x1
                  PUSH1 0x0
                  RETURN
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=10000000)
    
        bytecode = unhexlify('603760005360005160005560016000f3')
        world.create_account(address=0xcd1722f3947def4cf144679da39c4c32bdc35681,
                             balance=23,
                             code=bytecode,
                            )
        address = 0xcd1722f3947def4cf144679da39c4c32bdc35681
        price = 0x5af3107a4000
        data = unhexlify('aa')
        caller = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        value = 23
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
        account_address = 0xcd1722f3947def4cf144679da39c4c32bdc35681
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 23)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('603760005360005160005560016000f3'))
        #check storage
        self.assertEqual(world.get_storage_data(account_address, 0x00), 0x3700000000000000000000000000000000000000000000000000000000000000)
        #check outs
        self.assertEqual(returndata, unhexlify('37'))
        #check logs
        data = rlp.encode([Log(unhexlify('%040x'%l.address), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test spent gas
        self.assertEqual(new_vm.gas, 79973)

if __name__ == '__main__':
    unittest.main()
