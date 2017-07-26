
import struct
import unittest
import json
from manticore.platforms import evm
from manticore.core import state
from manticore.core.smtlib import Operators, ConstraintSet
import os


class EVMTest_vmBlockInfoTest(unittest.TestCase):
    _multiprocess_can_split_ = True
    maxDiff=None 

    def test_blockhashInRange(self):
        header ={
                   'coinbase': 244687034288125203496486448490407391986876152250L,
                   'difficulty': 256L,
                   'gaslimit': 1000000L,
                   'number': 257L,
                   'timestamp': 1L
                  }
        pos_world = {
                            87579061662017136990230301793909925042452127430L: {
                             'nonce': 0L,
                             'balance': 100000000000000000000000L,
                             'code': '`\x01@`\x00U`\x02@`\x01Ua\x01\x00@`\x02U',
                             'storage': {
                              0L: 90743482286830539503240959006302832933333810038750515972785732718729991261126L,
                              1L: 78469846343542442363028680824980501212021332975324075417961003849793346933925L,
                              2L: 49141853235351966986450010456217574961379676238517164466470671864163950076078L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=100000000000000000000000L, 
                                code='`\x01@`\x00U`\x02@`\x01Ua\x01\x00@`\x02U', 
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

    def test_blockhashMyBlock(self):
        header ={
                   'coinbase': 244687034288125203496486448490407391986876152250L,
                   'difficulty': 256L,
                   'gaslimit': 1000000L,
                   'number': 1L,
                   'timestamp': 1L
                  }
        pos_world = {
                            87579061662017136990230301793909925042452127430L: {
                             'nonce': 0L,
                             'balance': 100000000000000000000000L,
                             'code': '`\x01@`\x00U',
                             'storage': {
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=100000000000000000000000L, 
                                code='`\x01@`\x00U', 
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

    def test_blockhash258Block(self):
        header ={
                   'coinbase': 244687034288125203496486448490407391986876152250L,
                   'difficulty': 256L,
                   'gaslimit': 1000000L,
                   'number': 258L,
                   'timestamp': 1L
                  }
        pos_world = {
                            87579061662017136990230301793909925042452127430L: {
                             'nonce': 0L,
                             'balance': 100000000000000000000000L,
                             'code': '`\x01@`\x00U',
                             'storage': {
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=100000000000000000000000L, 
                                code='`\x01@`\x00U', 
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

    def test_gaslimit(self):
        header ={
                   'coinbase': 244687034288125203496486448490407391986876152250L,
                   'difficulty': 256L,
                   'gaslimit': 1000000L,
                   'number': 0L,
                   'timestamp': 1L
                  }
        pos_world = {
                            87579061662017136990230301793909925042452127430L: {
                             'nonce': 0L,
                             'balance': 100000000000000000000000L,
                             'code': 'E`\x00U',
                             'storage': {
                              0L: 1000000L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=100000000000000000000000L, 
                                code='E`\x00U', 
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

    def test_number(self):
        header ={
                   'coinbase': 244687034288125203496486448490407391986876152250L,
                   'difficulty': 256L,
                   'gaslimit': 1000000L,
                   'number': 1L,
                   'timestamp': 1L
                  }
        pos_world = {
                            87579061662017136990230301793909925042452127430L: {
                             'nonce': 0L,
                             'balance': 100000000000000000000000L,
                             'code': 'C`\x00U',
                             'storage': {
                              0L: 1L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=100000000000000000000000L, 
                                code='C`\x00U', 
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

    def test_blockhashOutOfRange(self):
        header ={
                   'coinbase': 244687034288125203496486448490407391986876152250L,
                   'difficulty': 256L,
                   'gaslimit': 1000000L,
                   'number': 257L,
                   'timestamp': 1L
                  }
        pos_world = {
                            87579061662017136990230301793909925042452127430L: {
                             'nonce': 0L,
                             'balance': 100000000000000000000000L,
                             'code': '`\x00@`\x00Ua\x01\x01@`\x01U\x7f\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff@`\x02U',
                             'storage': {
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=100000000000000000000000L, 
                                code='`\x00@`\x00Ua\x01\x01@`\x01U\x7f\xff\xff\xff\xff\xff\xff\xff\xff\xff'\
                                     '\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff'\
                                     '@`\x02U', 
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

    def test_blockhash257Block(self):
        header ={
                   'coinbase': 244687034288125203496486448490407391986876152250L,
                   'difficulty': 256L,
                   'gaslimit': 1000000L,
                   'number': 257L,
                   'timestamp': 1L
                  }
        pos_world = {
                            87579061662017136990230301793909925042452127430L: {
                             'nonce': 0L,
                             'balance': 100000000000000000000000L,
                             'code': '`\x00@`\x00U',
                             'storage': {
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=100000000000000000000000L, 
                                code='`\x00@`\x00U', 
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

    def test_difficulty(self):
        header ={
                   'coinbase': 244687034288125203496486448490407391986876152250L,
                   'difficulty': 256L,
                   'gaslimit': 1000000L,
                   'number': 0L,
                   'timestamp': 1L
                  }
        pos_world = {
                            87579061662017136990230301793909925042452127430L: {
                             'nonce': 0L,
                             'balance': 100000000000000000000000L,
                             'code': 'D`\x00U',
                             'storage': {
                              0L: 256L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=100000000000000000000000L, 
                                code='D`\x00U', 
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

    def test_blockhashUnderFlow(self):
        header ={
                   'coinbase': 244687034288125203496486448490407391986876152250L,
                   'difficulty': 256L,
                   'gaslimit': 1000000L,
                   'number': 1L,
                   'timestamp': 1L
                  }
        pos_world = None

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=100000000000000000000000L, 
                                code='@', 
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

    def test_timestamp(self):
        header ={
                   'coinbase': 244687034288125203496486448490407391986876152250L,
                   'difficulty': 256L,
                   'gaslimit': 1000000L,
                   'number': 0L,
                   'timestamp': 1L
                  }
        pos_world = {
                            87579061662017136990230301793909925042452127430L: {
                             'nonce': 0L,
                             'balance': 100000000000000000000000L,
                             'code': 'B`\x00U',
                             'storage': {
                              0L: 1L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=100000000000000000000000L, 
                                code='B`\x00U', 
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

    def test_coinbase(self):
        header ={
                   'coinbase': 244687034288125203496486448490407391986876152250L,
                   'difficulty': 256L,
                   'gaslimit': 1000000L,
                   'number': 0L,
                   'timestamp': 1L
                  }
        pos_world = {
                            87579061662017136990230301793909925042452127430L: {
                             'nonce': 0L,
                             'balance': 100000000000000000000000L,
                             'code': 'A`\x00U',
                             'storage': {
                              0L: 244687034288125203496486448490407391986876152250L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=100000000000000000000000L, 
                                code='A`\x00U', 
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

    def test_blockhashNotExistingBlock(self):
        header ={
                   'coinbase': 244687034288125203496486448490407391986876152250L,
                   'difficulty': 256L,
                   'gaslimit': 1000000L,
                   'number': 1L,
                   'timestamp': 1L
                  }
        pos_world = {
                            87579061662017136990230301793909925042452127430L: {
                             'nonce': 0L,
                             'balance': 100000000000000000000000L,
                             'code': '`\x02@`\x00U',
                             'storage': {
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=100000000000000000000000L, 
                                code='`\x02@`\x00U', 
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
