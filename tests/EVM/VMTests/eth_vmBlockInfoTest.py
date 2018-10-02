
#Taken from folder /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmBlockInfoTest
import struct
import unittest
import json
import os
from binascii import unhexlify
from manticore.platforms import evm
from manticore.core import state
from manticore.core.smtlib import Operators, ConstraintSet

class EVMTest_vmBlockInfoTest(unittest.TestCase):
    _multiprocess_can_split_ = True
    maxDiff=None 


    def test_coinbase(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmBlockInfoTest/coinbase.json
            sha256sum: e1bc11e92d785fc2a8d9f7b6f0d9dfd8fff91b95c6a14efd3167f2aab5cb91c2
            Code: COINBASE
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=100000000000000000000000,
                             code=unhexlify('41600055'),
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f3947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        bytecode = world.get_code(address)
        gas = 100000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = ''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = e.data
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 100000000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('41600055'))
        #check storage
        self.assertEqual(world.get_storage_data(account_address, 0x00), 0x2adc25665018aa1fe0e6bc666dac8fc2697ff9ba)
        # test spent gas
        self.assertEqual(new_vm.gas, 79995)
        #check callcreates
        #check refund
        #check logs
        

    def test_gaslimit(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmBlockInfoTest/gaslimit.json
            sha256sum: 1e488536fc1db36ff13c0dcd4f82a1ee035b5fb6ea593bf05c88982547b73faf
            Code: GASLIMIT
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=100000000000000000000000,
                             code=unhexlify('45600055'),
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f3947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        bytecode = world.get_code(address)
        gas = 100000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = ''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = e.data
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 100000000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('45600055'))
        #check storage
        self.assertEqual(world.get_storage_data(account_address, 0x00), 0x0f4240)
        # test spent gas
        self.assertEqual(new_vm.gas, 79995)
        #check callcreates
        #check refund
        #check logs
        

    def test_timestamp(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmBlockInfoTest/timestamp.json
            sha256sum: 9bce0f164941940231840afe8aa5f80177931a5e92d7f4c36a3f33e8621caf8b
            Code: TIMESTAMP
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=100000000000000000000000,
                             code=unhexlify('42600055'),
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f3947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        bytecode = world.get_code(address)
        gas = 100000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = ''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = e.data
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 100000000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('42600055'))
        #check storage
        self.assertEqual(world.get_storage_data(account_address, 0x00), 0x01)
        # test spent gas
        self.assertEqual(new_vm.gas, 79995)
        #check callcreates
        #check refund
        #check logs
        

    def test_difficulty(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmBlockInfoTest/difficulty.json
            sha256sum: ca2729ed6e20d0fe5c157f1de7ba9da1f49b8b22dc44b831c86996910c7b6fce
            Code: DIFFICULTY
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=100000000000000000000000,
                             code=unhexlify('44600055'),
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f3947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        bytecode = world.get_code(address)
        gas = 100000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = ''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = e.data
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 100000000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('44600055'))
        #check storage
        self.assertEqual(world.get_storage_data(account_address, 0x00), 0x0100)
        # test spent gas
        self.assertEqual(new_vm.gas, 79995)
        #check callcreates
        #check refund
        #check logs
        

    def test_number(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmBlockInfoTest/number.json
            sha256sum: 1d7812b3a8b4eb9b8d1c64dca8e52c0be8385e4dd66be877ff3c559a39364573
            Code: NUMBER
                  PUSH1 0x0
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=1, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=100000000000000000000000,
                             code=unhexlify('43600055'),
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f3947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        bytecode = world.get_code(address)
        gas = 100000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = ''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = e.data
        #Add pos checks for account hex(account_address)
        account_address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 100000000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('43600055'))
        #check storage
        self.assertEqual(world.get_storage_data(account_address, 0x00), 0x01)
        # test spent gas
        self.assertEqual(new_vm.gas, 79995)
        #check callcreates
        #check refund
        #check logs
        

if __name__ == '__main__':
    unittest.main()
