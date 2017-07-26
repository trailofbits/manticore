
import struct
import unittest
import json
from manticore.platforms import evm
from manticore.core import state
from manticore.core.smtlib import Operators, ConstraintSet
import os


class EVMTest_vmtests(unittest.TestCase):
    _multiprocess_can_split_ = True
    maxDiff=None 

    def test_suicide(self):
        header ={
                   'coinbase': 244687034288125203496486448490407391986876152250L,
                   'difficulty': 256L,
                   'gaslimit': 1000000L,
                   'number': 0L,
                   'timestamp': 1L
                  }
        pos_world = {
                            1170859069862169782511871033392474246841492526721L: {
                             'nonce': 0L,
                             'balance': 100000000000000000000000L,
                             'code': '',
                             'storage': {
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=100000000000000000000000L, 
                                code='3\xff', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069862169782511871033392474246841492526721L
        price = 100000000000000L
        data = ''
        caller = 1170859069862169782511871033392474246841492526721L
        value = 1000000000000000000L        
        platform.transaction(address, origin, price, data, caller, value, header)
        
        throw = False
        try:
            platform.run()
        except state.TerminateState as e:                
            if e.message != 'STOP':
                throw = True

        if pos_world is None:
            self.assertTrue(throw)
        else:
            self.assertEqual( pos_world, platform.storage)

    def test_arith(self):
        header ={
                   'coinbase': 244687034288125203496486448490407391986876152250L,
                   'difficulty': 256L,
                   'gaslimit': 1000000L,
                   'number': 0L,
                   'timestamp': 1L
                  }
        pos_world = None

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=100000000000000000000000L, 
                                code='`\x00`\x00`\x00`\x00`\x02`\x02`\x08\x03\x03`\x02`\x03\x06`\x02'\
                                     '`\x02\x04`\x04`\x04`\x04\x02\x02`\x02`\x02\x01\x01\x01\x01\x013`\xc8'\
                                     'Z\x03\xf1', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069862169782511871033392474246841492526721L
        price = 100000000000000L
        data = ''
        caller = 1170859069862169782511871033392474246841492526721L
        value = 1000000000000000000L        
        platform.transaction(address, origin, price, data, caller, value, header)
        
        throw = False
        try:
            platform.run()
        except state.TerminateState as e:                
            if e.message != 'STOP':
                throw = True

        if pos_world is None:
            self.assertTrue(throw)
        else:
            self.assertEqual( pos_world, platform.storage)

    def test_boolean(self):
        header ={
                   'coinbase': 244687034288125203496486448490407391986876152250L,
                   'difficulty': 256L,
                   'gaslimit': 1000000L,
                   'number': 0L,
                   'timestamp': 1L
                  }
        pos_world = None

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=100000000000000000000000L, 
                                code='`\x01`\x01\x16\x15`\x1aW`\x00`\x00`\x00`\x00`\x023`\xc8Z'\
                                     '\x03\xf1P[`\x00`\x01\x16\x15`5W`\x00`\x00`\x00`\x00`\x03'\
                                     '3`\xc8Z\x03\xf1P[`\x01`\x00\x16\x15`PW`\x00`\x00`\x00'\
                                     '`\x00`\x043`\xc8Z\x03\xf1P[`\x00`\x00\x16\x15`kW`\x00'\
                                     '`\x00`\x00`\x00`\x053`\xc8Z\x03\xf1P[`\x01`\x01\x17\x15`'\
                                     '\x86W`\x00`\x00`\x00`\x00`\x0c3`\xc8Z\x03\xf1P[`\x00`'\
                                     '\x01\x17\x15`\xa1W`\x00`\x00`\x00`\x00`\r3`\xc8Z\x03\xf1P'\
                                     '[`\x01`\x00\x17\x15`\xbcW`\x00`\x00`\x00`\x00`\x0e3`\xc8'\
                                     'Z\x03\xf1P[`\x00`\x00\x17\x15`\xd7W`\x00`\x00`\x00`\x00`'\
                                     '\x0f3`\xc8Z\x03\xf1P[', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069862169782511871033392474246841492526721L
        price = 100000000000000L
        data = ''
        caller = 1170859069862169782511871033392474246841492526721L
        value = 1000000000000000000L        
        platform.transaction(address, origin, price, data, caller, value, header)
        
        throw = False
        try:
            platform.run()
        except state.TerminateState as e:                
            if e.message != 'STOP':
                throw = True

        if pos_world is None:
            self.assertTrue(throw)
        else:
            self.assertEqual( pos_world, platform.storage)

    def test_mktx(self):
        header ={
                   'coinbase': 244687034288125203496486448490407391986876152250L,
                   'difficulty': 256L,
                   'gaslimit': 1000000L,
                   'number': 0L,
                   'timestamp': 1L
                  }
        pos_world = None

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=100000000000000000000000L, 
                                code='`\x00`\x00`\x00`\x00g\x06\xf0[Y\xd3\xb2\x00\x003`\xc8Z\x03\xf1', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069862169782511871033392474246841492526721L
        price = 100000000000000L
        data = ''
        caller = 1170859069862169782511871033392474246841492526721L
        value = 1000000000000000000L        
        platform.transaction(address, origin, price, data, caller, value, header)
        
        throw = False
        try:
            platform.run()
        except state.TerminateState as e:                
            if e.message != 'STOP':
                throw = True

        if pos_world is None:
            self.assertTrue(throw)
        else:
            self.assertEqual( pos_world, platform.storage)


if __name__ == '__main__':
    unittest.main()
