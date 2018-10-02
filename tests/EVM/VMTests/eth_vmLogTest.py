
#Taken from folder /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmLogTest
import struct
import unittest
import json
import os
from binascii import unhexlify
from manticore.platforms import evm
from manticore.core import state
from manticore.core.smtlib import Operators, ConstraintSet

class EVMTest_vmLogTest(unittest.TestCase):
    _multiprocess_can_split_ = True
    maxDiff=None 


    def test_log1_emptyMem(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmLogTest/log1_emptyMem.json
            sha256sum: 71f788143ff4d3f63bf13888864aa096bcfbfcba0ebbc52ccd3f36641d270913
            Code: PUSH1 0x0
                  PUSH1 0x0
                  PUSH1 0x0
                  LOG1
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=100000000000000000000000,
                             code=unhexlify('600060006000a1'),
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
        self.assertEqual(world.get_code(account_address), unhexlify('600060006000a1'))
        # test spent gas
        self.assertEqual(new_vm.gas, 99241)
        #check callcreates
        #check refund
        #check logs
        

    def test_log0_emptyMem(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmLogTest/log0_emptyMem.json
            sha256sum: c3a284136d4b139ed82230a498c71438eb668a4088f5a738345533a0bf96057c
            Code: PUSH1 0x0
                  PUSH1 0x0
                  LOG0
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=100000000000000000000000,
                             code=unhexlify('60006000a0'),
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
        self.assertEqual(world.get_code(account_address), unhexlify('60006000a0'))
        # test spent gas
        self.assertEqual(new_vm.gas, 99619)
        #check callcreates
        #check refund
        #check logs
        

    def test_log4_nonEmptyMem_logMemSize1_logMemStart31(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmLogTest/log4_nonEmptyMem_logMemSize1_logMemStart31.json
            sha256sum: 56c8911fc76941d080781ce7efe7d7e67e94fef0fdb4909a1705a92dc953c004
            Code: PUSH32 0xaabbffffffffffffffffffffffffffffffffffffffffffffffffffffffffccdd
                  PUSH1 0x0
                  MSTORE
                  PUSH1 0x0
                  PUSH1 0x0
                  PUSH1 0x0
                  PUSH1 0x0
                  PUSH1 0x1
                  PUSH1 0x1f
                  LOG4
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=100000000000000000000000,
                             code=unhexlify('7faabbffffffffffffffffffffffffffffffffffffffffffffffffffffffffccdd60005260006000600060006001601fa4'),
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
        self.assertEqual(world.get_code(account_address), unhexlify('7faabbffffffffffffffffffffffffffffffffffffffffffffffffffffffffccdd60005260006000600060006001601fa4'))
        # test spent gas
        self.assertEqual(new_vm.gas, 98087)
        #check callcreates
        #check refund
        #check logs
        

    def test_log2_logMemsizeZero(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmLogTest/log2_logMemsizeZero.json
            sha256sum: 2de0f99a2448351a187c2a51bad278945c0c0f390d42fc41d41e3cd9cc3beab5
            Code: PUSH32 0xaabbffffffffffffffffffffffffffffffffffffffffffffffffffffffffccdd
                  PUSH1 0x0
                  MSTORE
                  PUSH1 0x0
                  PUSH1 0x0
                  PUSH1 0x0
                  PUSH1 0x1
                  LOG2
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=100000000000000000000000,
                             code=unhexlify('7faabbffffffffffffffffffffffffffffffffffffffffffffffffffffffffccdd6000526000600060006001a2'),
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
        self.assertEqual(world.get_code(account_address), unhexlify('7faabbffffffffffffffffffffffffffffffffffffffffffffffffffffffffccdd6000526000600060006001a2'))
        # test spent gas
        self.assertEqual(new_vm.gas, 98851)
        #check callcreates
        #check refund
        #check logs
        

    def test_log3_logMemsizeZero(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmLogTest/log3_logMemsizeZero.json
            sha256sum: 1be6865fd2fdd62ba8a8b85f9b638dbe70fd4e38a93263916ed1f2fc0c7e4362
            Code: PUSH32 0xaabbffffffffffffffffffffffffffffffffffffffffffffffffffffffffccdd
                  PUSH1 0x0
                  MSTORE
                  PUSH1 0x0
                  PUSH1 0x0
                  PUSH1 0x0
                  PUSH1 0x0
                  PUSH1 0x1
                  LOG3
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=100000000000000000000000,
                             code=unhexlify('7faabbffffffffffffffffffffffffffffffffffffffffffffffffffffffffccdd60005260006000600060006001a3'),
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
        self.assertEqual(world.get_code(account_address), unhexlify('7faabbffffffffffffffffffffffffffffffffffffffffffffffffffffffffccdd60005260006000600060006001a3'))
        # test spent gas
        self.assertEqual(new_vm.gas, 98473)
        #check callcreates
        #check refund
        #check logs
        

    def test_log0_nonEmptyMem_logMemSize1(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmLogTest/log0_nonEmptyMem_logMemSize1.json
            sha256sum: 8720fe7acbee878520dfdc25b4a7ad6fe217d84969ac478f84f08628b0db69f7
            Code: PUSH32 0xaabbffffffffffffffffffffffffffffffffffffffffffffffffffffffffccdd
                  PUSH1 0x0
                  MSTORE
                  PUSH1 0x1
                  PUSH1 0x0
                  LOG0
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=100000000000000000000000,
                             code=unhexlify('7faabbffffffffffffffffffffffffffffffffffffffffffffffffffffffffccdd60005260016000a0'),
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
        self.assertEqual(world.get_code(account_address), unhexlify('7faabbffffffffffffffffffffffffffffffffffffffffffffffffffffffffccdd60005260016000a0'))
        # test spent gas
        self.assertEqual(new_vm.gas, 99599)
        #check callcreates
        #check refund
        #check logs
        

    def test_log3_nonEmptyMem_logMemSize1_logMemStart31(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmLogTest/log3_nonEmptyMem_logMemSize1_logMemStart31.json
            sha256sum: 3ba27188b55a255130ba7c7683ecc51e7b03be99c45767de29c31948cc732912
            Code: PUSH32 0xaabbffffffffffffffffffffffffffffffffffffffffffffffffffffffffccdd
                  PUSH1 0x0
                  MSTORE
                  PUSH1 0x0
                  PUSH1 0x0
                  PUSH1 0x0
                  PUSH1 0x1
                  PUSH1 0x1f
                  LOG3
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=100000000000000000000000,
                             code=unhexlify('7faabbffffffffffffffffffffffffffffffffffffffffffffffffffffffffccdd6000526000600060006001601fa3'),
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
        self.assertEqual(world.get_code(account_address), unhexlify('7faabbffffffffffffffffffffffffffffffffffffffffffffffffffffffffccdd6000526000600060006001601fa3'))
        # test spent gas
        self.assertEqual(new_vm.gas, 98465)
        #check callcreates
        #check refund
        #check logs
        

    def test_log2_nonEmptyMem(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmLogTest/log2_nonEmptyMem.json
            sha256sum: 2fbe4932f998e51ec4a7b4c439f288326946720c707a0c5fea6fa1244d66b236
            Code: PUSH32 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
                  PUSH1 0x0
                  MSTORE
                  PUSH1 0x0
                  PUSH1 0x0
                  PUSH1 0x20
                  PUSH1 0x0
                  LOG2
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=100000000000000000000000,
                             code=unhexlify('7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff6000526000600060206000a2'),
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
        self.assertEqual(world.get_code(account_address), unhexlify('7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff6000526000600060206000a2'))
        # test spent gas
        self.assertEqual(new_vm.gas, 98595)
        #check callcreates
        #check refund
        #check logs
        

    def test_log0_nonEmptyMem(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmLogTest/log0_nonEmptyMem.json
            sha256sum: 4809c2eb5c78f1dad2654794124cd4baeff293e67144a0fcddde1de97048788b
            Code: PUSH32 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
                  PUSH1 0x0
                  MSTORE
                  PUSH1 0x20
                  PUSH1 0x0
                  LOG0
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=100000000000000000000000,
                             code=unhexlify('7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff60005260206000a0'),
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
        self.assertEqual(world.get_code(account_address), unhexlify('7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff60005260206000a0'))
        # test spent gas
        self.assertEqual(new_vm.gas, 99351)
        #check callcreates
        #check refund
        #check logs
        

    def test_log3_logMemsizeTooHigh(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmLogTest/log3_logMemsizeTooHigh.json
            sha256sum: af09b71ba8eab3c0c1870be53f962140d8b53d251677a051abad3a6269a1576d
            Code: PUSH32 0xaabbffffffffffffffffffffffffffffffffffffffffffffffffffffffffccdd
                  PUSH1 0x0
                  MSTORE
                  PUSH1 0x0
                  PUSH1 0x0
                  PUSH1 0x0
                  PUSH32 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
                  PUSH1 0x1
                  LOG3
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=100000000000000000000000,
                             code=unhexlify('7faabbffffffffffffffffffffffffffffffffffffffffffffffffffffffffccdd6000526000600060007fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff6001a3'),
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
        #If test end in exception ceck it here
        self.assertTrue(result in ('THROW'))

    def test_log4_logMemsizeZero(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmLogTest/log4_logMemsizeZero.json
            sha256sum: b9a2ef73cdde2f36aa3ec4aa09780c6b2741a81fd86c075718680d50f2246d30
            Code: PUSH32 0xaabbffffffffffffffffffffffffffffffffffffffffffffffffffffffffccdd
                  PUSH1 0x0
                  MSTORE
                  PUSH1 0x0
                  PUSH1 0x0
                  PUSH1 0x0
                  PUSH1 0x0
                  PUSH1 0x0
                  PUSH1 0x1
                  LOG4
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=100000000000000000000000,
                             code=unhexlify('7faabbffffffffffffffffffffffffffffffffffffffffffffffffffffffffccdd600052600060006000600060006001a4'),
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
        self.assertEqual(world.get_code(account_address), unhexlify('7faabbffffffffffffffffffffffffffffffffffffffffffffffffffffffffccdd600052600060006000600060006001a4'))
        # test spent gas
        self.assertEqual(new_vm.gas, 98095)
        #check callcreates
        #check refund
        #check logs
        

    def test_log0_logMemStartTooHigh(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmLogTest/log0_logMemStartTooHigh.json
            sha256sum: 4046b1bf04e8ca250287b3c37c485ebd4e5fa4178f2c732c34055cfa578284fd
            Code: PUSH32 0xaabbffffffffffffffffffffffffffffffffffffffffffffffffffffffffccdd
                  PUSH1 0x0
                  MSTORE
                  PUSH1 0x1
                  PUSH32 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
                  LOG0
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=100000000000000000000000,
                             code=unhexlify('7faabbffffffffffffffffffffffffffffffffffffffffffffffffffffffffccdd60005260017fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffa0'),
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
        #If test end in exception ceck it here
        self.assertTrue(result in ('THROW'))

    def test_log0_nonEmptyMem_logMemSize1_logMemStart31(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmLogTest/log0_nonEmptyMem_logMemSize1_logMemStart31.json
            sha256sum: 40ef6dfb1334bcdd8e22ebfaa134b2c678fbd4da537434236525f3a15e723eb6
            Code: PUSH32 0xaabbffffffffffffffffffffffffffffffffffffffffffffffffffffffffccdd
                  PUSH1 0x0
                  MSTORE
                  PUSH1 0x1
                  PUSH1 0x1f
                  LOG0
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=100000000000000000000000,
                             code=unhexlify('7faabbffffffffffffffffffffffffffffffffffffffffffffffffffffffffccdd6000526001601fa0'),
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
        self.assertEqual(world.get_code(account_address), unhexlify('7faabbffffffffffffffffffffffffffffffffffffffffffffffffffffffffccdd6000526001601fa0'))
        # test spent gas
        self.assertEqual(new_vm.gas, 99599)
        #check callcreates
        #check refund
        #check logs
        

    def test_log3_nonEmptyMem(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmLogTest/log3_nonEmptyMem.json
            sha256sum: 0d6eda924af19f4265f1ce517ece10f36d1fd937da060b9efb7f7d0ffd04708f
            Code: PUSH32 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
                  PUSH1 0x0
                  MSTORE
                  PUSH1 0x0
                  PUSH1 0x0
                  PUSH1 0x0
                  PUSH1 0x20
                  PUSH1 0x0
                  LOG3
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=100000000000000000000000,
                             code=unhexlify('7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff60005260006000600060206000a3'),
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
        self.assertEqual(world.get_code(account_address), unhexlify('7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff60005260006000600060206000a3'))
        # test spent gas
        self.assertEqual(new_vm.gas, 98217)
        #check callcreates
        #check refund
        #check logs
        

    def test_log3_PC(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmLogTest/log3_PC.json
            sha256sum: da3adfdeed4a88fb877cd2834c4a84e400ba6f673bdb496c6846feae3fc994ea
            Code: PUSH1 0xff
                  PUSH1 0x0
                  MSTORE8
                  GETPC
                  GETPC
                  GETPC
                  PUSH1 0x20
                  PUSH1 0x0
                  LOG3
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=100000000000000000000000,
                             code=unhexlify('60ff60005358585860206000a3'),
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
        self.assertEqual(world.get_code(account_address), unhexlify('60ff60005358585860206000a3'))
        # test spent gas
        self.assertEqual(new_vm.gas, 98220)
        #check callcreates
        #check refund
        #check logs
        

    def test_log4_emptyMem(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmLogTest/log4_emptyMem.json
            sha256sum: 073ce194300d6d1463f3fbb0151a1e9ae6bdbdb4a39916ccfc8af156ae8d53cc
            Code: PUSH1 0x0
                  PUSH1 0x0
                  PUSH1 0x0
                  PUSH1 0x0
                  PUSH1 0x0
                  PUSH1 0x0
                  LOG4
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=100000000000000000000000,
                             code=unhexlify('600060006000600060006000a4'),
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
        self.assertEqual(world.get_code(account_address), unhexlify('600060006000600060006000a4'))
        # test spent gas
        self.assertEqual(new_vm.gas, 98107)
        #check callcreates
        #check refund
        #check logs
        

    def test_log_2logs(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmLogTest/log_2logs.json
            sha256sum: 4c25e8b02f238d5a895e94ec497ae4037e4ae5d13b19faf7b5b3d3bdba6366f4
            Code: PUSH32 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
                  PUSH1 0x0
                  MSTORE
                  PUSH1 0x20
                  PUSH1 0x0
                  LOG0
                  PUSH1 0x10
                  PUSH1 0x2
                  LOG0
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=100000000000000000000000,
                             code=unhexlify('7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff60005260206000a060106002a0'),
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
        self.assertEqual(world.get_code(account_address), unhexlify('7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff60005260206000a060106002a0'))
        # test spent gas
        self.assertEqual(new_vm.gas, 98842)
        #check callcreates
        #check refund
        #check logs
        

    def test_log1_logMemsizeTooHigh(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmLogTest/log1_logMemsizeTooHigh.json
            sha256sum: b9aea166d34a86889061864034fec55cc0f2ae5080a3c50afafbef75ed92f564
            Code: PUSH32 0xaabbffffffffffffffffffffffffffffffffffffffffffffffffffffffffccdd
                  PUSH1 0x0
                  MSTORE
                  PUSH1 0x0
                  PUSH32 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
                  PUSH1 0x1
                  LOG1
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=100000000000000000000000,
                             code=unhexlify('7faabbffffffffffffffffffffffffffffffffffffffffffffffffffffffffccdd60005260007fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff6001a1'),
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
        #If test end in exception ceck it here
        self.assertTrue(result in ('THROW'))

    def test_log4_logMemsizeTooHigh(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmLogTest/log4_logMemsizeTooHigh.json
            sha256sum: 82728d076ff2ae0a081c7c84c8dc912f42c453a083c6f7a0ae5794e98d96ea3e
            Code: PUSH32 0xaabbffffffffffffffffffffffffffffffffffffffffffffffffffffffffccdd
                  PUSH1 0x0
                  MSTORE
                  PUSH1 0x0
                  PUSH1 0x0
                  PUSH1 0x0
                  PUSH1 0x0
                  PUSH32 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
                  PUSH1 0x1
                  LOG4
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=100000000000000000000000,
                             code=unhexlify('7faabbffffffffffffffffffffffffffffffffffffffffffffffffffffffffccdd60005260006000600060007fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff6001a4'),
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
        #If test end in exception ceck it here
        self.assertTrue(result in ('THROW'))

    def test_log1_logMemsizeZero(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmLogTest/log1_logMemsizeZero.json
            sha256sum: e3ea5f4a2229c7b3d54759bebcfd6e7776645087c922978f1eb32607027c2c41
            Code: PUSH32 0xaabbffffffffffffffffffffffffffffffffffffffffffffffffffffffffccdd
                  PUSH1 0x0
                  MSTORE
                  PUSH1 0x0
                  PUSH1 0x0
                  PUSH1 0x1
                  LOG1
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=100000000000000000000000,
                             code=unhexlify('7faabbffffffffffffffffffffffffffffffffffffffffffffffffffffffffccdd600052600060006001a1'),
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
        self.assertEqual(world.get_code(account_address), unhexlify('7faabbffffffffffffffffffffffffffffffffffffffffffffffffffffffffccdd600052600060006001a1'))
        # test spent gas
        self.assertEqual(new_vm.gas, 99229)
        #check callcreates
        #check refund
        #check logs
        

    def test_log4_nonEmptyMem(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmLogTest/log4_nonEmptyMem.json
            sha256sum: 6074e18b72197353c2d9a67596394153b23c0df9dfc4fda551e0e5cefb597256
            Code: PUSH32 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
                  PUSH1 0x0
                  MSTORE
                  PUSH1 0x0
                  PUSH1 0x0
                  PUSH1 0x0
                  PUSH1 0x0
                  PUSH1 0x20
                  PUSH1 0x0
                  LOG4
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=100000000000000000000000,
                             code=unhexlify('7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff600052600060006000600060206000a4'),
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
        self.assertEqual(world.get_code(account_address), unhexlify('7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff600052600060006000600060206000a4'))
        # test spent gas
        self.assertEqual(new_vm.gas, 97839)
        #check callcreates
        #check refund
        #check logs
        

    def test_log2_nonEmptyMem_logMemSize1_logMemStart31(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmLogTest/log2_nonEmptyMem_logMemSize1_logMemStart31.json
            sha256sum: a7ec4949eed7b0156a9542e618e1c16faf61e469869c232265a44d756eb70e44
            Code: PUSH32 0xaabbffffffffffffffffffffffffffffffffffffffffffffffffffffffffccdd
                  PUSH1 0x0
                  MSTORE
                  PUSH1 0x0
                  PUSH1 0x0
                  PUSH1 0x1
                  PUSH1 0x1f
                  LOG2
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=100000000000000000000000,
                             code=unhexlify('7faabbffffffffffffffffffffffffffffffffffffffffffffffffffffffffccdd600052600060006001601fa2'),
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
        self.assertEqual(world.get_code(account_address), unhexlify('7faabbffffffffffffffffffffffffffffffffffffffffffffffffffffffffccdd600052600060006001601fa2'))
        # test spent gas
        self.assertEqual(new_vm.gas, 98843)
        #check callcreates
        #check refund
        #check logs
        

    def test_log2_logMemStartTooHigh(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmLogTest/log2_logMemStartTooHigh.json
            sha256sum: 1afa6e3c119e91f5ad62b53ac9588efd43c91277707747d0e03b760d21a68938
            Code: PUSH32 0xaabbffffffffffffffffffffffffffffffffffffffffffffffffffffffffccdd
                  PUSH1 0x0
                  MSTORE
                  PUSH1 0x0
                  PUSH1 0x0
                  PUSH1 0x1
                  PUSH32 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
                  LOG2
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=100000000000000000000000,
                             code=unhexlify('7faabbffffffffffffffffffffffffffffffffffffffffffffffffffffffffccdd6000526000600060017fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffa2'),
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
        #If test end in exception ceck it here
        self.assertTrue(result in ('THROW'))

    def test_log3_MaxTopic(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmLogTest/log3_MaxTopic.json
            sha256sum: ee9b5129c6d7eecc7462f3ad9b856a81d900ced092684674f6eeff1cce9c4df2
            Code: PUSH32 0xaabbffffffffffffffffffffffffffffffffffffffffffffffffffffffffccdd
                  PUSH1 0x0
                  MSTORE
                  PUSH32 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
                  PUSH32 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
                  PUSH32 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
                  PUSH1 0x20
                  PUSH1 0x0
                  LOG3
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=100000000000000000000000,
                             code=unhexlify('7faabbffffffffffffffffffffffffffffffffffffffffffffffffffffffffccdd6000527fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff60206000a3'),
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
        self.assertEqual(world.get_code(account_address), unhexlify('7faabbffffffffffffffffffffffffffffffffffffffffffffffffffffffffccdd6000527fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff60206000a3'))
        # test spent gas
        self.assertEqual(new_vm.gas, 98217)
        #check callcreates
        #check refund
        #check logs
        

    def test_log1_nonEmptyMem(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmLogTest/log1_nonEmptyMem.json
            sha256sum: 56e94300e9740f76e9797f7f0cc018b363346ce9c4e8e81730d497cc78ec6afe
            Code: PUSH32 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
                  PUSH1 0x0
                  MSTORE
                  PUSH1 0x0
                  PUSH1 0x20
                  PUSH1 0x0
                  LOG1
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=100000000000000000000000,
                             code=unhexlify('7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff600052600060206000a1'),
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
        self.assertEqual(world.get_code(account_address), unhexlify('7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff600052600060206000a1'))
        # test spent gas
        self.assertEqual(new_vm.gas, 98973)
        #check callcreates
        #check refund
        #check logs
        

    def test_log1_Caller(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmLogTest/log1_Caller.json
            sha256sum: 1d220bc5200563e038c5a785e850b5a7e2cf826a40f2f583edda1e604c2f5a03
            Code: PUSH1 0xff
                  PUSH1 0x0
                  MSTORE8
                  CALLER
                  PUSH1 0x20
                  PUSH1 0x0
                  LOG1
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=100000000000000000000000,
                             code=unhexlify('60ff6000533360206000a1'),
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
        self.assertEqual(world.get_code(account_address), unhexlify('60ff6000533360206000a1'))
        # test spent gas
        self.assertEqual(new_vm.gas, 98974)
        #check callcreates
        #check refund
        #check logs
        

    def test_log3_Caller(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmLogTest/log3_Caller.json
            sha256sum: 2057aeb1b01ee459f27dfa1fc200ecac3a15af48807ded7da414c72258e44ec5
            Code: PUSH1 0xff
                  PUSH1 0x0
                  MSTORE8
                  CALLER
                  PUSH1 0x0
                  PUSH1 0x0
                  PUSH1 0x20
                  PUSH1 0x0
                  LOG3
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=100000000000000000000000,
                             code=unhexlify('60ff600053336000600060206000a3'),
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
        self.assertEqual(world.get_code(account_address), unhexlify('60ff600053336000600060206000a3'))
        # test spent gas
        self.assertEqual(new_vm.gas, 98218)
        #check callcreates
        #check refund
        #check logs
        

    def test_log4_PC(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmLogTest/log4_PC.json
            sha256sum: 958db35842289a91f83f5a8c3ec4d0def9d193a5d5fa91813ed783c254eb65a3
            Code: PUSH1 0xff
                  PUSH1 0x0
                  MSTORE8
                  GETPC
                  GETPC
                  GETPC
                  GETPC
                  PUSH1 0x20
                  PUSH1 0x0
                  LOG4
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=100000000000000000000000,
                             code=unhexlify('60ff6000535858585860206000a4'),
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
        self.assertEqual(world.get_code(account_address), unhexlify('60ff6000535858585860206000a4'))
        # test spent gas
        self.assertEqual(new_vm.gas, 97843)
        #check callcreates
        #check refund
        #check logs
        

    def test_log3_nonEmptyMem_logMemSize1(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmLogTest/log3_nonEmptyMem_logMemSize1.json
            sha256sum: d7c1833e69d1358182160d8f4fd698e64b627dffd619d93c0adaddc9cc4ef7d1
            Code: PUSH32 0xaabbffffffffffffffffffffffffffffffffffffffffffffffffffffffffccdd
                  PUSH1 0x0
                  MSTORE
                  PUSH1 0x0
                  PUSH1 0x0
                  PUSH1 0x0
                  PUSH1 0x1
                  PUSH1 0x0
                  LOG3
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=100000000000000000000000,
                             code=unhexlify('7faabbffffffffffffffffffffffffffffffffffffffffffffffffffffffffccdd60005260006000600060016000a3'),
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
        self.assertEqual(world.get_code(account_address), unhexlify('7faabbffffffffffffffffffffffffffffffffffffffffffffffffffffffffccdd60005260006000600060016000a3'))
        # test spent gas
        self.assertEqual(new_vm.gas, 98465)
        #check callcreates
        #check refund
        #check logs
        

    def test_log4_logMemStartTooHigh(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmLogTest/log4_logMemStartTooHigh.json
            sha256sum: 8db9aff06068b33ea4e3e9e4a1f637f5a720dfa08de4760c8ec68f476d0b35f8
            Code: PUSH32 0xaabbffffffffffffffffffffffffffffffffffffffffffffffffffffffffccdd
                  PUSH1 0x0
                  MSTORE
                  PUSH1 0x0
                  PUSH1 0x0
                  PUSH1 0x0
                  PUSH1 0x0
                  PUSH1 0x1
                  PUSH32 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
                  LOG4
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=100000000000000000000000,
                             code=unhexlify('7faabbffffffffffffffffffffffffffffffffffffffffffffffffffffffffccdd600052600060006000600060017fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffa4'),
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
        #If test end in exception ceck it here
        self.assertTrue(result in ('THROW'))

    def test_log3_emptyMem(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmLogTest/log3_emptyMem.json
            sha256sum: 8c9391e1de2b11d24d08c2b79d1a7e1fedff3a558957f8114acc46901d5289c0
            Code: PUSH1 0x0
                  PUSH1 0x0
                  PUSH1 0x0
                  PUSH1 0x0
                  PUSH1 0x0
                  LOG3
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=100000000000000000000000,
                             code=unhexlify('60006000600060006000a3'),
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
        self.assertEqual(world.get_code(account_address), unhexlify('60006000600060006000a3'))
        # test spent gas
        self.assertEqual(new_vm.gas, 98485)
        #check callcreates
        #check refund
        #check logs
        

    def test_log1_nonEmptyMem_logMemSize1_logMemStart31(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmLogTest/log1_nonEmptyMem_logMemSize1_logMemStart31.json
            sha256sum: eb3aeb44e7bf15f6b9e2f803b8ecf8e17eff0f0fa4af1c68b2f5913b7019d667
            Code: PUSH32 0xaabbffffffffffffffffffffffffffffffffffffffffffffffffffffffffccdd
                  PUSH1 0x0
                  MSTORE
                  PUSH1 0x0
                  PUSH1 0x1
                  PUSH1 0x1f
                  LOG1
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=100000000000000000000000,
                             code=unhexlify('7faabbffffffffffffffffffffffffffffffffffffffffffffffffffffffffccdd60005260006001601fa1'),
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
        self.assertEqual(world.get_code(account_address), unhexlify('7faabbffffffffffffffffffffffffffffffffffffffffffffffffffffffffccdd60005260006001601fa1'))
        # test spent gas
        self.assertEqual(new_vm.gas, 99221)
        #check callcreates
        #check refund
        #check logs
        

    def test_log2_emptyMem(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmLogTest/log2_emptyMem.json
            sha256sum: d8cb8d7f0912ea30fc84df6cec7b7c22a59a73868440f1a1cae815c46b030566
            Code: PUSH1 0x0
                  PUSH1 0x0
                  PUSH1 0x0
                  PUSH1 0x0
                  LOG2
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=100000000000000000000000,
                             code=unhexlify('6000600060006000a2'),
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
        self.assertEqual(world.get_code(account_address), unhexlify('6000600060006000a2'))
        # test spent gas
        self.assertEqual(new_vm.gas, 98863)
        #check callcreates
        #check refund
        #check logs
        

    def test_log4_nonEmptyMem_logMemSize1(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmLogTest/log4_nonEmptyMem_logMemSize1.json
            sha256sum: 30625d2e7b7e7549ec1422def098ca70c481a34a287e2eda4c398b2202041e42
            Code: PUSH32 0xaabbffffffffffffffffffffffffffffffffffffffffffffffffffffffffccdd
                  PUSH1 0x0
                  MSTORE
                  PUSH1 0x0
                  PUSH1 0x0
                  PUSH1 0x0
                  PUSH1 0x0
                  PUSH1 0x1
                  PUSH1 0x0
                  LOG4
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=100000000000000000000000,
                             code=unhexlify('7faabbffffffffffffffffffffffffffffffffffffffffffffffffffffffffccdd600052600060006000600060016000a4'),
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
        self.assertEqual(world.get_code(account_address), unhexlify('7faabbffffffffffffffffffffffffffffffffffffffffffffffffffffffffccdd600052600060006000600060016000a4'))
        # test spent gas
        self.assertEqual(new_vm.gas, 98087)
        #check callcreates
        #check refund
        #check logs
        

    def test_log3_logMemStartTooHigh(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmLogTest/log3_logMemStartTooHigh.json
            sha256sum: dafef6520cbed526376e3ea1377e9c51e850d9297caed1cf66bc41df8e10252d
            Code: PUSH32 0xaabbffffffffffffffffffffffffffffffffffffffffffffffffffffffffccdd
                  PUSH1 0x0
                  MSTORE
                  PUSH1 0x0
                  PUSH1 0x0
                  PUSH1 0x0
                  PUSH1 0x1
                  PUSH32 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
                  LOG3
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=100000000000000000000000,
                             code=unhexlify('7faabbffffffffffffffffffffffffffffffffffffffffffffffffffffffffccdd60005260006000600060017fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffa3'),
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
        #If test end in exception ceck it here
        self.assertTrue(result in ('THROW'))

    def test_log1_MaxTopic(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmLogTest/log1_MaxTopic.json
            sha256sum: b87182f7fdf74e68d2ce84a7d88f2d81b25167fd2f5cae70ec38834e3be3bd4d
            Code: PUSH32 0xaabbffffffffffffffffffffffffffffffffffffffffffffffffffffffffccdd
                  PUSH1 0x0
                  MSTORE
                  PUSH32 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
                  PUSH1 0x20
                  PUSH1 0x0
                  LOG1
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=100000000000000000000000,
                             code=unhexlify('7faabbffffffffffffffffffffffffffffffffffffffffffffffffffffffffccdd6000527fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff60206000a1'),
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
        self.assertEqual(world.get_code(account_address), unhexlify('7faabbffffffffffffffffffffffffffffffffffffffffffffffffffffffffccdd6000527fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff60206000a1'))
        # test spent gas
        self.assertEqual(new_vm.gas, 98973)
        #check callcreates
        #check refund
        #check logs
        

    def test_log0_logMemsizeZero(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmLogTest/log0_logMemsizeZero.json
            sha256sum: e40443d743dffc5df6ac9accd055ba81e0accce8525dd021f2e4b82546ea811f
            Code: PUSH32 0xaabbffffffffffffffffffffffffffffffffffffffffffffffffffffffffccdd
                  PUSH1 0x0
                  MSTORE
                  PUSH1 0x0
                  PUSH1 0x1
                  LOG0
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=100000000000000000000000,
                             code=unhexlify('7faabbffffffffffffffffffffffffffffffffffffffffffffffffffffffffccdd60005260006001a0'),
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
        self.assertEqual(world.get_code(account_address), unhexlify('7faabbffffffffffffffffffffffffffffffffffffffffffffffffffffffffccdd60005260006001a0'))
        # test spent gas
        self.assertEqual(new_vm.gas, 99607)
        #check callcreates
        #check refund
        #check logs
        

    def test_log1_nonEmptyMem_logMemSize1(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmLogTest/log1_nonEmptyMem_logMemSize1.json
            sha256sum: 640d458608d2bf8ca0a6559e020ff8a499ce8fbcd6f5376f4c8e6e4825426022
            Code: PUSH32 0xaabbffffffffffffffffffffffffffffffffffffffffffffffffffffffffccdd
                  PUSH1 0x0
                  MSTORE
                  PUSH1 0x0
                  PUSH1 0x1
                  PUSH1 0x0
                  LOG1
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=100000000000000000000000,
                             code=unhexlify('7faabbffffffffffffffffffffffffffffffffffffffffffffffffffffffffccdd600052600060016000a1'),
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
        self.assertEqual(world.get_code(account_address), unhexlify('7faabbffffffffffffffffffffffffffffffffffffffffffffffffffffffffccdd600052600060016000a1'))
        # test spent gas
        self.assertEqual(new_vm.gas, 99221)
        #check callcreates
        #check refund
        #check logs
        

    def test_log2_MaxTopic(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmLogTest/log2_MaxTopic.json
            sha256sum: 2c0cb9233cbd96f88f618415646b802e9c2ab0341673cfb5aaa801250faa8c45
            Code: PUSH32 0xaabbffffffffffffffffffffffffffffffffffffffffffffffffffffffffccdd
                  PUSH1 0x0
                  MSTORE
                  PUSH32 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
                  PUSH32 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
                  PUSH1 0x20
                  PUSH1 0x0
                  LOG2
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=100000000000000000000000,
                             code=unhexlify('7faabbffffffffffffffffffffffffffffffffffffffffffffffffffffffffccdd6000527fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff60206000a2'),
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
        self.assertEqual(world.get_code(account_address), unhexlify('7faabbffffffffffffffffffffffffffffffffffffffffffffffffffffffffccdd6000527fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff60206000a2'))
        # test spent gas
        self.assertEqual(new_vm.gas, 98595)
        #check callcreates
        #check refund
        #check logs
        

    def test_log4_MaxTopic(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmLogTest/log4_MaxTopic.json
            sha256sum: 25f0995468aad81a0d781f22a45906ab6d16136b50a23a4b2db229e944834952
            Code: PUSH32 0xaabbffffffffffffffffffffffffffffffffffffffffffffffffffffffffccdd
                  PUSH1 0x0
                  MSTORE
                  PUSH32 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
                  PUSH32 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
                  PUSH32 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
                  PUSH32 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
                  PUSH1 0x20
                  PUSH1 0x0
                  LOG4
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=100000000000000000000000,
                             code=unhexlify('7faabbffffffffffffffffffffffffffffffffffffffffffffffffffffffffccdd6000527fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff60206000a4'),
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
        self.assertEqual(world.get_code(account_address), unhexlify('7faabbffffffffffffffffffffffffffffffffffffffffffffffffffffffffccdd6000527fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff60206000a4'))
        # test spent gas
        self.assertEqual(new_vm.gas, 97839)
        #check callcreates
        #check refund
        #check logs
        

    def test_log4_Caller(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmLogTest/log4_Caller.json
            sha256sum: cc4e075e4c0d4ed03e53ddab5b06c796ee79c29570af92b545995c50b61fee2d
            Code: PUSH1 0xff
                  PUSH1 0x0
                  MSTORE8
                  CALLER
                  PUSH1 0x0
                  PUSH1 0x0
                  PUSH1 0x0
                  PUSH1 0x20
                  PUSH1 0x0
                  LOG4
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=100000000000000000000000,
                             code=unhexlify('60ff6000533360006000600060206000a4'),
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
        self.assertEqual(world.get_code(account_address), unhexlify('60ff6000533360006000600060206000a4'))
        # test spent gas
        self.assertEqual(new_vm.gas, 97840)
        #check callcreates
        #check refund
        #check logs
        

    def test_log0_logMemsizeTooHigh(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmLogTest/log0_logMemsizeTooHigh.json
            sha256sum: 1ed2c5ffa25641c6c4bdfab3955700f05fbd988b0fd1a9bfd4d6b81b74b5e701
            Code: PUSH32 0xaabbffffffffffffffffffffffffffffffffffffffffffffffffffffffffccdd
                  PUSH1 0x0
                  MSTORE
                  PUSH32 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
                  PUSH1 0x1
                  LOG0
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=100000000000000000000000,
                             code=unhexlify('7faabbffffffffffffffffffffffffffffffffffffffffffffffffffffffffccdd6000527fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff6001a0'),
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
        #If test end in exception ceck it here
        self.assertTrue(result in ('THROW'))

    def test_log2_logMemsizeTooHigh(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmLogTest/log2_logMemsizeTooHigh.json
            sha256sum: 3c48e9ea58196af71d991910c7ea68a2b8778cca9f5e283f67e947e4a429f767
            Code: PUSH32 0xaabbffffffffffffffffffffffffffffffffffffffffffffffffffffffffccdd
                  PUSH1 0x0
                  MSTORE
                  PUSH1 0x0
                  PUSH1 0x0
                  PUSH32 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
                  PUSH1 0x1
                  LOG2
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=100000000000000000000000,
                             code=unhexlify('7faabbffffffffffffffffffffffffffffffffffffffffffffffffffffffffccdd600052600060007fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff6001a2'),
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
        #If test end in exception ceck it here
        self.assertTrue(result in ('THROW'))

    def test_log1_logMemStartTooHigh(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmLogTest/log1_logMemStartTooHigh.json
            sha256sum: 91d86b400d333e9b9e5b3e57b7b075b25533cd1bef9b9075fa5399d6b49c964c
            Code: PUSH32 0xaabbffffffffffffffffffffffffffffffffffffffffffffffffffffffffccdd
                  PUSH1 0x0
                  MSTORE
                  PUSH1 0x0
                  PUSH1 0x1
                  PUSH32 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
                  LOG1
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=100000000000000000000000,
                             code=unhexlify('7faabbffffffffffffffffffffffffffffffffffffffffffffffffffffffffccdd600052600060017fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffa1'),
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
        #If test end in exception ceck it here
        self.assertTrue(result in ('THROW'))

    def test_log2_nonEmptyMem_logMemSize1(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmLogTest/log2_nonEmptyMem_logMemSize1.json
            sha256sum: 2bf4b91ae90206e77f7484eced239875b84e9262368d19b57338b01bd90c8d9a
            Code: PUSH32 0xaabbffffffffffffffffffffffffffffffffffffffffffffffffffffffffccdd
                  PUSH1 0x0
                  MSTORE
                  PUSH1 0x0
                  PUSH1 0x0
                  PUSH1 0x1
                  PUSH1 0x0
                  LOG2
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=100000000000000000000000,
                             code=unhexlify('7faabbffffffffffffffffffffffffffffffffffffffffffffffffffffffffccdd6000526000600060016000a2'),
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
        self.assertEqual(world.get_code(account_address), unhexlify('7faabbffffffffffffffffffffffffffffffffffffffffffffffffffffffffccdd6000526000600060016000a2'))
        # test spent gas
        self.assertEqual(new_vm.gas, 98843)
        #check callcreates
        #check refund
        #check logs
        

    def test_log2_Caller(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmLogTest/log2_Caller.json
            sha256sum: e4b2caf359c6a99848c76a8865b8647c7940de5ac8e5eb88c5e15d61064cdd85
            Code: PUSH1 0xff
                  PUSH1 0x0
                  MSTORE8
                  CALLER
                  PUSH1 0x0
                  PUSH1 0x20
                  PUSH1 0x0
                  LOG2
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=100000000000000000000000,
                             code=unhexlify('60ff60005333600060206000a2'),
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
        self.assertEqual(world.get_code(account_address), unhexlify('60ff60005333600060206000a2'))
        # test spent gas
        self.assertEqual(new_vm.gas, 98596)
        #check callcreates
        #check refund
        #check logs
        

if __name__ == '__main__':
    unittest.main()
