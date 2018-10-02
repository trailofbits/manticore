
#Taken from folder /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmRandomTest
import struct
import unittest
import json
import os
from binascii import unhexlify
from manticore.platforms import evm
from manticore.core import state
from manticore.core.smtlib import Operators, ConstraintSet

class EVMTest_vmRandomTest(unittest.TestCase):
    _multiprocess_can_split_ = True
    maxDiff=None 


    def test_201503110346PYTHON_PUSH24(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmRandomTest/201503110346PYTHON_PUSH24.json
            sha256sum: 9e1fe28512255a4e232969ef18c2edc5a8f014c4162701fe85e4185fc4eb94df
            Code: 
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=300, timestamp=2, difficulty=115792089237316195423570985008687907853269984665640564039457584007913129639935, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=unhexlify('7745414245403745f31387900a8d55'),
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f3947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        bytecode = world.get_code(address)
        gas = 10000

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
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('7745414245403745f31387900a8d55'))
        # test spent gas
        self.assertEqual(new_vm.gas, 9997)
        #check callcreates
        #check refund
        #check logs
        

    def test_201503110219PYTHON(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmRandomTest/201503110219PYTHON.json
            sha256sum: 5303a9f6647b6d7a04a2465debcfa7ee54374519b1e84c214d81fe59472c02ee
            Code: 
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=300, timestamp=2, difficulty=115792089237316195423570985008687907853269984665640564039457584007913129639935, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=unhexlify('4040459143404144809759886d608f'),
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f3947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        bytecode = world.get_code(address)
        gas = 10000

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

    def test_201503111844PYTHON(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmRandomTest/201503111844PYTHON.json
            sha256sum: 1f250eac1ff00b8e033fe61fdac154443ecaa4d518f640afe32d551e42a0e63e
            Code: 
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=300, timestamp=2, difficulty=115792089237316195423570985008687907853269984665640564039457584007913129639935, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=unhexlify('65424555'),
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f3947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        bytecode = world.get_code(address)
        gas = 10000

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
        self.assertEqual(world.get_balance(account_address), 1000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('65424555'))
        # test spent gas
        self.assertEqual(new_vm.gas, 9997)
        #check callcreates
        #check refund
        #check logs
        

    def test_201503102320PYTHON(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmRandomTest/201503102320PYTHON.json
            sha256sum: 013b742a81aac58b74efba9901735369d6291fe9e089cc5791391e75d3acf9b7
            Code: NUMBER
                  NUMBER
                  TIMESTAMP
                  DIFFICULTY
                  TIMESTAMP
                  DIFFICULTY
                  GASLIMIT
                  GASLIMIT
                  SWAP8
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=300, timestamp=2, difficulty=115792089237316195423570985008687907853269984665640564039457584007913129639935, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=unhexlify('434342444244454597'),
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f3947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        bytecode = world.get_code(address)
        gas = 10000

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

    def test_201503110206PYTHON(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmRandomTest/201503110206PYTHON.json
            sha256sum: 1eb97bd94fc8e15148f69509cc06549ed16f0efdf28be03840ebef305b0ced73
            Code: BLOCKHASH
                  GASLIMIT
                  BLOCKHASH
                  COINBASE
                  GASLIMIT
                  GASLIMIT
                  DIFFICULTY
                  COINBASE
                  CALLVALUE
                  CODECOPY
                  DUP8
                  SELFDESTRUCT
                  CALLDATACOPY
                  CALLDATALOAD
                  DIV
                  ADDRESS
                  SSTORE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=300, timestamp=2, difficulty=115792089237316195423570985008687907853269984665640564039457584007913129639935, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=unhexlify('4045404145454441343987ff3735043055'),
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f3947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        bytecode = world.get_code(address)
        gas = 10000

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

    def test_201503112218PYTHON(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmRandomTest/201503112218PYTHON.json
            sha256sum: f05e99434999a6f8e5b2f84972d1459072636f68528c5caba349f1afb4fe9ddc
            Code: BLOCKHASH
                  COINBASE
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=300, timestamp=2, difficulty=115792089237316195423570985008687907853269984665640564039457584007913129639935, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=1000000000000000000,
                             code=unhexlify('4041'),
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f3947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        bytecode = world.get_code(address)
        gas = 10000

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

if __name__ == '__main__':
    unittest.main()
