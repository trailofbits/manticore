
#Taken from folder /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmTests
import struct
import unittest
import json
import os
from binascii import unhexlify
from manticore.platforms import evm
from manticore.core import state
from manticore.core.smtlib import Operators, ConstraintSet

class EVMTest_vmTests(unittest.TestCase):
    _multiprocess_can_split_ = True
    maxDiff=None 


    def test_suicide(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmTests/suicide.json
            sha256sum: 441b14435343d9d30fed7a31aa183a4f7be30f735cf3aaa6595ddee23c2096df
            Code: CALLER
                  SELFDESTRUCT
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=100000000000000000000000,
                             code=unhexlify('33ff'),
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
        account_address = 0xcd1722f3947def4cf144679da39c4c32bdc35681
        #check nonce
        self.assertEqual(world.get_nonce(account_address), 0)
        #check balance
        self.assertEqual(world.get_balance(account_address), 100000000000000000000000)
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify(''))
        # test spent gas
        self.assertEqual(new_vm.gas, 99998)
        #check callcreates
        #check refund
        #check logs
        

if __name__ == '__main__':
    unittest.main()
