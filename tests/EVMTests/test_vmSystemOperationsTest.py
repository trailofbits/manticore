
import struct
import unittest
import json
from manticore.platforms import evm
from manticore.core import state
from manticore.core.smtlib import Operators, ConstraintSet
import os


class EVMTest_vmSystemOperationsTest(unittest.TestCase):
    _multiprocess_can_split_ = True
    maxDiff=None 

    def test_callstatelessToNameRegistrator0(self):
        header ={
                   'coinbase': 244687034288125203496486448490407391986876152250L,
                   'difficulty': 256L,
                   'gaslimit': 10000000L,
                   'number': 0L,
                   'timestamp': 1L
                  }
        pos_world = {
                            846782024548323446991784721256445173708587954613L: {
                             'nonce': 0L,
                             'balance': 23L,
                             'code': '`\x005T\x15`\tW\x00[` 5`\x005U',
                             'storage': {
                             }
                            },
                            87579061662017136990230301793909925042452127430L: {
                             'nonce': 0L,
                             'balance': 100000000000000000000000L,
                             'code': '\x7f\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff`\x00R\x7f\xaa\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xaa` '\
                             'R`\x00`@`@`\x00`\x17s\x94S\x04\xeb\x96\x06[*\x98\xb5zH\xa0j\xe2\x8d(Zq\xb5b\x0fB@\xf1`\x00U',
                             'storage': {
                              0L: 1L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=846782024548323446991784721256445173708587954613L, 
                                balance=23L, 
                                code='`\x005T\x15`\tW\x00[` 5`\x005U', 
                                storage={
                                        }
                                )           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=100000000000000000000000L, 
                                code='\x7f\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff'\
                                     '\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff`\x00R\x7f\xaa\xff\xff\xff\xff\xff\xff\xff\xff'\
                                     '\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xaa'\
                                     '` R`\x00`@`@`\x00`\x17s\x94S\x04\xeb\x96\x06[*\x98'\
                                     '\xb5zH\xa0j\xe2\x8d(Zq\xb5b\x0fB@\xf1`\x00U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069862169782511871033392474246841492526721L
        price = 100000000000000L
        data = ''
        caller = 1170859069862169782511871033392474246841492526721L
        value = 100000L        
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

    def test_createNameRegistratorValueTooHigh(self):
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
                             'balance': 100L,
                             'code': '|`\x10\x80`\x0c`\x009`\x00\xf3\x00`\x005T\x15`\tW\x00[` 5`\x005U`\x00R`\x1d`\x03`\xe6\xf0`\x00U',
                             'storage': {
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=100L, 
                                code='|`\x10\x80`\x0c`\x009`\x00\xf3\x00`\x005T\x15`\tW\x00['\
                                     '` 5`\x005U`\x00R`\x1d`\x03`\xe6\xf0`\x00U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069862169782511871033392474246841492526721L
        price = 100000000000000L
        data = ''
        caller = 1170859069862169782511871033392474246841492526721L
        value = 100L        
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

    def test_CallToReturn1(self):
        header ={
                   'coinbase': 244687034288125203496486448490407391986876152250L,
                   'difficulty': 256L,
                   'gaslimit': 10000000L,
                   'number': 0L,
                   'timestamp': 1L
                  }
        pos_world = {
                            846782024548323446991784721256445173708587954613L: {
                             'nonce': 0L,
                             'balance': 23L,
                             'code': '`\x01`\x01W`7`\x00U`\x02`\x00\xf2',
                             'storage': {
                             }
                            },
                            87579061662017136990230301793909925042452127430L: {
                             'nonce': 0L,
                             'balance': 100000000000000000000000L,
                             'code': '\x7f\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff`\x00R\x7f\xaa\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xaa` '\
                             'R`\x02`\x00`@`\x00`\x17s\x94S\x04\xeb\x96\x06[*\x98\xb5zH\xa0j\xe2\x8d(Zq\xb5b\x0fB@\xf1`\x00U',
                             'storage': {
                              0L: 1L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=846782024548323446991784721256445173708587954613L, 
                                balance=23L, 
                                code='`\x01`\x01W`7`\x00U`\x02`\x00\xf2', 
                                storage={
                                        }
                                )           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=100000000000000000000000L, 
                                code='\x7f\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff'\
                                     '\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff`\x00R\x7f\xaa\xff\xff\xff\xff\xff\xff\xff\xff'\
                                     '\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xaa'\
                                     '` R`\x02`\x00`@`\x00`\x17s\x94S\x04\xeb\x96\x06[*\x98'\
                                     '\xb5zH\xa0j\xe2\x8d(Zq\xb5b\x0fB@\xf1`\x00U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069862169782511871033392474246841492526721L
        price = 100000000000000L
        data = ''
        caller = 1170859069862169782511871033392474246841492526721L
        value = 100000L        
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

    def test_CallToNameRegistrator0(self):
        header ={
                   'coinbase': 244687034288125203496486448490407391986876152250L,
                   'difficulty': 256L,
                   'gaslimit': 10000000L,
                   'number': 0L,
                   'timestamp': 1L
                  }
        pos_world = {
                            846782024548323446991784721256445173708587954613L: {
                             'nonce': 0L,
                             'balance': 23L,
                             'code': '`\x005T\x15`\tW\x00[` 5`\x005U',
                             'storage': {
                             }
                            },
                            87579061662017136990230301793909925042452127430L: {
                             'nonce': 0L,
                             'balance': 100000000000000000000000L,
                             'code': '\x7f\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff`\x00R\x7f\xaa\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xaa` '\
                             'R`\x00`@`@`\x00`\x17s\x94S\x04\xeb\x96\x06[*\x98\xb5zH\xa0j\xe2\x8d(Zq\xb5b\x0fB@\xf1`\x00U',
                             'storage': {
                              0L: 1L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=846782024548323446991784721256445173708587954613L, 
                                balance=23L, 
                                code='`\x005T\x15`\tW\x00[` 5`\x005U', 
                                storage={
                                        }
                                )           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=100000000000000000000000L, 
                                code='\x7f\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff'\
                                     '\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff`\x00R\x7f\xaa\xff\xff\xff\xff\xff\xff\xff\xff'\
                                     '\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xaa'\
                                     '` R`\x00`@`@`\x00`\x17s\x94S\x04\xeb\x96\x06[*\x98'\
                                     '\xb5zH\xa0j\xe2\x8d(Zq\xb5b\x0fB@\xf1`\x00U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069862169782511871033392474246841492526721L
        price = 100000000000000L
        data = ''
        caller = 1170859069862169782511871033392474246841492526721L
        value = 100000L        
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

    def test_CallToNameRegistratorOutOfGas(self):
        header ={
                   'coinbase': 244687034288125203496486448490407391986876152250L,
                   'difficulty': 256L,
                   'gaslimit': 10000000L,
                   'number': 0L,
                   'timestamp': 1L
                  }
        pos_world = None

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=846782024548323446991784721256445173708587954613L, 
                                balance=23L, 
                                code='`\x005T\x15`\tW\x00[` 5`\x005U', 
                                storage={
                                        }
                                )           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=100000000000000000000000L, 
                                code='\x7f\xee\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff'\
                                     '\xff\xff\xff\xff\xff\xff\xff\xff\xff\x00`\x00R\x7f\xaa\xff\xff\xff\xff\xff\xff\xff\xff'\
                                     '\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xaa'\
                                     '` R`\x00`@`@`\x00`\x17s\x94S\x04\xeb\x96\x06[*\x98'\
                                     '\xb5zH\xa0j\xe2\x8d(Zq\xb5`d\xf1`\x00U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069862169782511871033392474246841492526721L
        price = 100000000000000L
        data = ''
        caller = 1170859069862169782511871033392474246841492526721L
        value = 100000L        
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

    def test_CallToNameRegistratorNotMuchMemory0(self):
        header ={
                   'coinbase': 244687034288125203496486448490407391986876152250L,
                   'difficulty': 256L,
                   'gaslimit': 10000000L,
                   'number': 0L,
                   'timestamp': 1L
                  }
        pos_world = None

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=846782024548323446991784721256445173708587954613L, 
                                balance=23L, 
                                code='`\x005T\x15`\tW\x00[` 5`\x005U', 
                                storage={
                                        }
                                )           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=100000000000000000000000L, 
                                code='\x7f\xee\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff'\
                                     '\xff\xff\xff\xff\xff\xff\xff\xff\xff\x00`\x00R\x7f\xaa\xff\xff\xff\xff\xff\xff\xff\xff'\
                                     '\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xaa'\
                                     '` R`\x00b\x0f\x12\x06`@`\x00`\x17s\x94S\x04\xeb\x96\x06['\
                                     '*\x98\xb5zH\xa0j\xe2\x8d(Zq\xb5a\x01\xf4\xf1`\x00U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069862169782511871033392474246841492526721L
        price = 100000000000000L
        data = ''
        caller = 1170859069862169782511871033392474246841492526721L
        value = 100000L        
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

    def test_CallToNameRegistratorNotMuchMemory1(self):
        header ={
                   'coinbase': 244687034288125203496486448490407391986876152250L,
                   'difficulty': 256L,
                   'gaslimit': 10000000L,
                   'number': 0L,
                   'timestamp': 1L
                  }
        pos_world = None

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=846782024548323446991784721256445173708587954613L, 
                                balance=23L, 
                                code='`\x005T\x15`\tW\x00[` 5`\x005U', 
                                storage={
                                        }
                                )           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=100000000000000000000000L, 
                                code='\x7f\xee\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff'\
                                     '\xff\xff\xff\xff\xff\xff\xff\xff\xff\x00`\x00R\x7f\xaa\xff\xff\xff\xff\xff\xff\xff\xff'\
                                     '\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xaa'\
                                     '` R`\x00`@`\x00b\x0f\x12\x06`\x17s\x94S\x04\xeb\x96\x06['\
                                     '*\x98\xb5zH\xa0j\xe2\x8d(Zq\xb5a\x01\xf4\xf1`\x00U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069862169782511871033392474246841492526721L
        price = 100000000000000L
        data = ''
        caller = 1170859069862169782511871033392474246841492526721L
        value = 100000L        
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

    @unittest.skip('Gas or performance related')
    def test_ABAcallsSuicide1(self):
        header ={
                   'coinbase': 244687034288125203496486448490407391986876152250L,
                   'difficulty': 256L,
                   'gaslimit': 10000000L,
                   'number': 0L,
                   'timestamp': 1L
                  }
        pos_world = {
                            846782024548323446991784721256445173708587954613L: {
                             'nonce': 0L,
                             'balance': 23L,
                             'code': '`\x00`\x00`\x00`\x00`\x17s\x0fW.R\x95\xc5\x7f\x15\x88o\x9b&>/m-l{^\xc6a\x01\xf4\xf1`\x01\x01XUs\x0fW.R\x95\xc5\x7f\x15\x88o\x9b&>/m-l{^\xc6\xff',
                             'storage': {
                             }
                            },
                            87579061662017136990230301793909925042452127430L: {
                             'nonce': 0L,
                             'balance': 100000000000000000000000L,
                             'code': '`\x00`\x00`\x00`\x00`\x18s\x94S\x04\xeb\x96\x06[*\x98\xb5zH\xa0j\xe2\x8d(Zq\xb5a\x03\xe8\xf1XU',
                             'storage': {
                              35L: 1L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=846782024548323446991784721256445173708587954613L, 
                                balance=23L, 
                                code='`\x00`\x00`\x00`\x00`\x17s\x0fW.R\x95\xc5\x7f\x15\x88o\x9b&'\
                                     '>/m-l{^\xc6a\x01\xf4\xf1`\x01\x01XUs\x0fW.R\x95'\
                                     '\xc5\x7f\x15\x88o\x9b&>/m-l{^\xc6\xff', 
                                storage={
                                        }
                                )           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=100000000000000000000000L, 
                                code='`\x00`\x00`\x00`\x00`\x18s\x94S\x04\xeb\x96\x06[*\x98\xb5zH'\
                                     '\xa0j\xe2\x8d(Zq\xb5a\x03\xe8\xf1XU', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069862169782511871033392474246841492526721L
        price = 100000000000000L
        data = ''
        caller = 1170859069862169782511871033392474246841492526721L
        value = 100000L        
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

    @unittest.skip('Gas or performance related')
    def test_ABAcallsSuicide0(self):
        header ={
                   'coinbase': 244687034288125203496486448490407391986876152250L,
                   'difficulty': 256L,
                   'gaslimit': 10000000L,
                   'number': 0L,
                   'timestamp': 1L
                  }
        pos_world = {
                            846782024548323446991784721256445173708587954613L: {
                             'nonce': 0L,
                             'balance': 100000000000000000000023L,
                             'code': '`\x00`\x00`\x00`\x00`\x17s\x0fW.R\x95\xc5\x7f\x15\x88o\x9b&>/m-l{^\xc6a\x01\xf4\xf1`\x01\x01XU',
                             'storage': {
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=846782024548323446991784721256445173708587954613L, 
                                balance=23L, 
                                code='`\x00`\x00`\x00`\x00`\x17s\x0fW.R\x95\xc5\x7f\x15\x88o\x9b&'\
                                     '>/m-l{^\xc6a\x01\xf4\xf1`\x01\x01XU', 
                                storage={
                                        }
                                )           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=100000000000000000000000L, 
                                code='`\x00`\x00`\x00`\x00`\x18s\x94S\x04\xeb\x96\x06[*\x98\xb5zH'\
                                     '\xa0j\xe2\x8d(Zq\xb5a\x03\xe8\xf1XUs\x94S\x04\xeb\x96\x06[*'\
                                     '\x98\xb5zH\xa0j\xe2\x8d(Zq\xb5\xff', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069862169782511871033392474246841492526721L
        price = 100000000000000L
        data = ''
        caller = 1170859069862169782511871033392474246841492526721L
        value = 100000L        
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

    def test_PostToNameRegistrator0(self):
        header ={
                   'coinbase': 244687034288125203496486448490407391986876152250L,
                   'difficulty': 256L,
                   'gaslimit': 10000000L,
                   'number': 0L,
                   'timestamp': 1L
                  }
        pos_world = {
                            846782024548323446991784721256445173708587954613L: {
                             'nonce': 0L,
                             'balance': 23L,
                             'code': '`\x005T\x15`\tW\x00[` 5`\x005U',
                             'storage': {
                             }
                            },
                            87579061662017136990230301793909925042452127430L: {
                             'nonce': 0L,
                             'balance': 100000000000000000000000L,
                             'code': '\x7f\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff`\x00R\x7f\xaa\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xaa` '\
                             'R`@`\x00`@`\x00`\x17s\x94S\x04\xeb\x96\x06[*\x98\xb5zH\xa0j\xe2\x8d(Zq\xb5b\x0fB@\xf1`\x00U',
                             'storage': {
                              0L: 1L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=846782024548323446991784721256445173708587954613L, 
                                balance=23L, 
                                code='`\x005T\x15`\tW\x00[` 5`\x005U', 
                                storage={
                                        }
                                )           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=100000000000000000000000L, 
                                code='\x7f\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff'\
                                     '\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff`\x00R\x7f\xaa\xff\xff\xff\xff\xff\xff\xff\xff'\
                                     '\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xaa'\
                                     '` R`@`\x00`@`\x00`\x17s\x94S\x04\xeb\x96\x06[*\x98'\
                                     '\xb5zH\xa0j\xe2\x8d(Zq\xb5b\x0fB@\xf1`\x00U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069862169782511871033392474246841492526721L
        price = 100000000000000L
        data = ''
        caller = 1170859069862169782511871033392474246841492526721L
        value = 100000L        
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

    def test_createNameRegistratorOutOfMemoryBonds1(self):
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
                                balance=100L, 
                                code='|`\x10\x80`\x0c`\x009`\x00\xf3\x00`\x005T\x15`\tW\x00['\
                                     '` 5`\x005U`\x00Rc\xff\xff\xff\xff`\x03`\x17\xf0`\x00U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069862169782511871033392474246841492526721L
        price = 100000000000000L
        data = ''
        caller = 1170859069862169782511871033392474246841492526721L
        value = 100L        
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

    def test_createNameRegistratorOutOfMemoryBonds0(self):
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
                                balance=100L, 
                                code='|`\x10\x80`\x0c`\x009`\x00\xf3\x00`\x005T\x15`\tW\x00['\
                                     '` 5`\x005U`\x00R`\x1de\x0f\xff\xff\xff\xff\xff`\x17\xf0`'\
                                     '\x00U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069862169782511871033392474246841492526721L
        price = 100000000000000L
        data = ''
        caller = 1170859069862169782511871033392474246841492526721L
        value = 100L        
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

    @unittest.skip('Gas or performance related')
    def test_CallToNameRegistratorTooMuchMemory1(self):
        header ={
                   'coinbase': 244687034288125203496486448490407391986876152250L,
                   'difficulty': 256L,
                   'gaslimit': 10000000L,
                   'number': 0L,
                   'timestamp': 1L
                  }
        pos_world = None

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=846782024548323446991784721256445173708587954613L, 
                                balance=23L, 
                                code='`\x005T\x15`\tW\x00[` 5`\x005U', 
                                storage={
                                        }
                                )           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=100000000000000000000000L, 
                                code='\x7f\xee\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff'\
                                     '\xff\xff\xff\xff\xff\xff\xff\xff\xff\x00`\x00R\x7f\xaa\xff\xff\xff\xff\xff\xff\xff\xff'\
                                     '\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xaa'\
                                     '` R`\x00`@b\x96\x88\xd8`\x00`\x17s\x94S\x04\xeb\x96\x06['\
                                     '*\x98\xb5zH\xa0j\xe2\x8d(Zq\xb5a\x01\xf4\xf1`\x00U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069862169782511871033392474246841492526721L
        price = 100000000000000L
        data = ''
        caller = 1170859069862169782511871033392474246841492526721L
        value = 100000L        
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

    def test_CallToNameRegistratorTooMuchMemory0(self):
        header ={
                   'coinbase': 244687034288125203496486448490407391986876152250L,
                   'difficulty': 256L,
                   'gaslimit': 10000000L,
                   'number': 0L,
                   'timestamp': 1L
                  }
        pos_world = None

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=846782024548323446991784721256445173708587954613L, 
                                balance=23L, 
                                code='`\x005T\x15`\tW\x00[` 5`\x005U', 
                                storage={
                                        }
                                )           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=100000000000000000000000L, 
                                code='\x7f\xee\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff'\
                                     '\xff\xff\xff\xff\xff\xff\xff\xff\xff\x00`\x00R\x7f\xaa\xff\xff\xff\xff\xff\xff\xff\xff'\
                                     '\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xaa'\
                                     '` R`\x00`@`@c:\xdeh\xb1`\x17s\x94S\x04\xeb\x96\x06'\
                                     '[*\x98\xb5zH\xa0j\xe2\x8d(Zq\xb5a\x01\xf4\xf1`\x00U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069862169782511871033392474246841492526721L
        price = 100000000000000L
        data = ''
        caller = 1170859069862169782511871033392474246841492526721L
        value = 100000L        
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

    def test_callcodeToReturn1(self):
        header ={
                   'coinbase': 244687034288125203496486448490407391986876152250L,
                   'difficulty': 256L,
                   'gaslimit': 10000000L,
                   'number': 0L,
                   'timestamp': 1L
                  }
        pos_world = {
                            846782024548323446991784721256445173708587954613L: {
                             'nonce': 0L,
                             'balance': 23L,
                             'code': '`\x01`\x01W`7`\x00U`\x02`\x00\xf2',
                             'storage': {
                             }
                            },
                            87579061662017136990230301793909925042452127430L: {
                             'nonce': 0L,
                             'balance': 100000000000000000000000L,
                             'code': '\x7f\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff`\x00R\x7f\xaa\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xaa` '\
                             'R`\x02`\x00`@`\x00`\x17s\x94S\x04\xeb\x96\x06[*\x98\xb5zH\xa0j\xe2\x8d(Zq\xb5a\x01\xf4\xf2`\x00U',
                             'storage': {
                              0L: 1L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=846782024548323446991784721256445173708587954613L, 
                                balance=23L, 
                                code='`\x01`\x01W`7`\x00U`\x02`\x00\xf2', 
                                storage={
                                        }
                                )           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=100000000000000000000000L, 
                                code='\x7f\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff'\
                                     '\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff`\x00R\x7f\xaa\xff\xff\xff\xff\xff\xff\xff\xff'\
                                     '\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xaa'\
                                     '` R`\x02`\x00`@`\x00`\x17s\x94S\x04\xeb\x96\x06[*\x98'\
                                     '\xb5zH\xa0j\xe2\x8d(Zq\xb5a\x01\xf4\xf2`\x00U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069862169782511871033392474246841492526721L
        price = 100000000000000L
        data = ''
        caller = 1170859069862169782511871033392474246841492526721L
        value = 100000L        
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

    def test_CallToNameRegistratorTooMuchMemory2(self):
        header ={
                   'coinbase': 244687034288125203496486448490407391986876152250L,
                   'difficulty': 256L,
                   'gaslimit': 10000000L,
                   'number': 0L,
                   'timestamp': 1L
                  }
        pos_world = None

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=846782024548323446991784721256445173708587954613L, 
                                balance=23L, 
                                code='`\x005T\x15`\tW\x00[` 5`\x005U', 
                                storage={
                                        }
                                )           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=100000000000000000000000L, 
                                code='\x7f\xee\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff'\
                                     '\xff\xff\xff\xff\xff\xff\xff\xff\xff\x00`\x00R\x7f\xaa\xff\xff\xff\xff\xff\xff\xff\xff'\
                                     '\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xaa'\
                                     '` R`\x01b\x0f\x12\x06`@`\x00`\x17s\x94S\x04\xeb\x96\x06['\
                                     '*\x98\xb5zH\xa0j\xe2\x8d(Zq\xb5a\x01\xf4\xf1`\x00U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069862169782511871033392474246841492526721L
        price = 100000000000000L
        data = ''
        caller = 1170859069862169782511871033392474246841492526721L
        value = 100000L        
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

    def test_callstatelessToReturn1(self):
        header ={
                   'coinbase': 244687034288125203496486448490407391986876152250L,
                   'difficulty': 256L,
                   'gaslimit': 10000000L,
                   'number': 0L,
                   'timestamp': 1L
                  }
        pos_world = {
                            846782024548323446991784721256445173708587954613L: {
                             'nonce': 0L,
                             'balance': 23L,
                             'code': '`\x01`\x01W`7`\x00U`\x02`\x00\xf2',
                             'storage': {
                             }
                            },
                            87579061662017136990230301793909925042452127430L: {
                             'nonce': 0L,
                             'balance': 100000000000000000000000L,
                             'code': '\x7f\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff`\x00R\x7f\xaa\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xaa` '\
                             'R`\x02`\x00`@`\x00`\x17s\x94S\x04\xeb\x96\x06[*\x98\xb5zH\xa0j\xe2\x8d(Zq\xb5a\x13\x88\xf1`\x00U',
                             'storage': {
                              0L: 1L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=846782024548323446991784721256445173708587954613L, 
                                balance=23L, 
                                code='`\x01`\x01W`7`\x00U`\x02`\x00\xf2', 
                                storage={
                                        }
                                )           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=100000000000000000000000L, 
                                code='\x7f\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff'\
                                     '\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff`\x00R\x7f\xaa\xff\xff\xff\xff\xff\xff\xff\xff'\
                                     '\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xaa'\
                                     '` R`\x02`\x00`@`\x00`\x17s\x94S\x04\xeb\x96\x06[*\x98'\
                                     '\xb5zH\xa0j\xe2\x8d(Zq\xb5a\x13\x88\xf1`\x00U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069862169782511871033392474246841492526721L
        price = 100000000000000L
        data = ''
        caller = 1170859069862169782511871033392474246841492526721L
        value = 100000L        
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

    def test_PostToReturn1(self):
        header ={
                   'coinbase': 244687034288125203496486448490407391986876152250L,
                   'difficulty': 256L,
                   'gaslimit': 10000000L,
                   'number': 0L,
                   'timestamp': 1L
                  }
        pos_world = {
                            846782024548323446991784721256445173708587954613L: {
                             'nonce': 0L,
                             'balance': 23L,
                             'code': '`7`\x00U`\x02`\x00\xf2',
                             'storage': {
                             }
                            },
                            87579061662017136990230301793909925042452127430L: {
                             'nonce': 0L,
                             'balance': 100000000000000000000000L,
                             'code': '\x7f\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff`\x00R\x7f\xaa\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xaa` '\
                             'R`@`\x00`@`\x00`\x17s\x94S\x04\xeb\x96\x06[*\x98\xb5zH\xa0j\xe2\x8d(Zq\xb5b\x0fB@\xf1`\x00U',
                             'storage': {
                              0L: 1L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=846782024548323446991784721256445173708587954613L, 
                                balance=23L, 
                                code='`7`\x00U`\x02`\x00\xf2', 
                                storage={
                                        }
                                )           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=100000000000000000000000L, 
                                code='\x7f\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff'\
                                     '\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff`\x00R\x7f\xaa\xff\xff\xff\xff\xff\xff\xff\xff'\
                                     '\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xaa'\
                                     '` R`@`\x00`@`\x00`\x17s\x94S\x04\xeb\x96\x06[*\x98'\
                                     '\xb5zH\xa0j\xe2\x8d(Zq\xb5b\x0fB@\xf1`\x00U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069862169782511871033392474246841492526721L
        price = 100000000000000L
        data = ''
        caller = 1170859069862169782511871033392474246841492526721L
        value = 100000L        
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

    def test_suicideNotExistingAccount(self):
        header ={
                   'coinbase': 244687034288125203496486448490407391986876152250L,
                   'difficulty': 256L,
                   'gaslimit': 10000000L,
                   'number': 0L,
                   'timestamp': 1L
                  }
        pos_world = {
                            971044392883335399163710997669544927747907999361L: {
                             'nonce': 0L,
                             'balance': 100000000000000000000000L,
                             'code': '',
                             'storage': {
                             }
                            },
                            1170859069862169782511871033392474246841492526721L: {
                             'nonce': 0L,
                             'balance': 23L,
                             'code': '`\x005T\x15`\tW\x00[` 5`\x005U',
                             'storage': {
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=1170859069862169782511871033392474246841492526721L, 
                                balance=23L, 
                                code='`\x005T\x15`\tW\x00[` 5`\x005U', 
                                storage={
                                        }
                                )           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=100000000000000000000000L, 
                                code='s\xaa\x17"\xf3\x94}\xefL\xf1Dg\x9d\xa3\x9cL2\xbd\xc3V\x81\xff', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069862169782511871033392474246841492526721L
        price = 100000000000000L
        data = ''
        caller = 1170859069862169782511871033392474246841492526721L
        value = 100000L        
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

    @unittest.skip('Gas or performance related')
    def test_callcodeToNameRegistrator0(self):
        header ={
                   'coinbase': 244687034288125203496486448490407391986876152250L,
                   'difficulty': 256L,
                   'gaslimit': 10000000L,
                   'number': 0L,
                   'timestamp': 1L
                  }
        pos_world = {
                            846782024548323446991784721256445173708587954613L: {
                             'nonce': 0L,
                             'balance': 23L,
                             'code': '`\x005T\x15`\tW\x00[` 5`\x005U',
                             'storage': {
                             }
                            },
                            87579061662017136990230301793909925042452127430L: {
                             'nonce': 0L,
                             'balance': 100000000000000000000000L,
                             'code': '\x7f\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff`\x00R\x7f\xaa\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xaa` '\
                             'R`\x00`@`@`\x00`\x17s\x94S\x04\xeb\x96\x06[*\x98\xb5zH\xa0j\xe2\x8d(Zq\xb5b\x0fB@\xf2`\x00U',
                             'storage': {
                              0L: 1L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=846782024548323446991784721256445173708587954613L, 
                                balance=23L, 
                                code='`\x005T\x15`\tW\x00[` 5`\x005U', 
                                storage={
                                        }
                                )           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=100000000000000000000000L, 
                                code='\x7f\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff'\
                                     '\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff`\x00R\x7f\xaa\xff\xff\xff\xff\xff\xff\xff\xff'\
                                     '\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xaa'\
                                     '` R`\x00`@`@`\x00`\x17s\x94S\x04\xeb\x96\x06[*\x98'\
                                     '\xb5zH\xa0j\xe2\x8d(Zq\xb5b\x0fB@\xf2`\x00U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069862169782511871033392474246841492526721L
        price = 100000000000000L
        data = ''
        caller = 1170859069862169782511871033392474246841492526721L
        value = 100000L        
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

    def test_suicide0(self):
        header ={
                   'coinbase': 244687034288125203496486448490407391986876152250L,
                   'difficulty': 256L,
                   'gaslimit': 10000000L,
                   'number': 0L,
                   'timestamp': 1L
                  }
        pos_world = {
                            1170859069862169782511871033392474246841492526721L: {
                             'nonce': 0L,
                             'balance': 100000000000000000000023L,
                             'code': '`\x005T\x15`\tW\x00[` 5`\x005U',
                             'storage': {
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=1170859069862169782511871033392474246841492526721L, 
                                balance=23L, 
                                code='`\x005T\x15`\tW\x00[` 5`\x005U', 
                                storage={
                                        }
                                )           
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
        value = 100000L        
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

    def test_suicideSendEtherToMe(self):
        header ={
                   'coinbase': 244687034288125203496486448490407391986876152250L,
                   'difficulty': 256L,
                   'gaslimit': 10000000L,
                   'number': 0L,
                   'timestamp': 1L
                  }
        pos_world = {
                            1170859069862169782511871033392474246841492526721L: {
                             'nonce': 0L,
                             'balance': 23L,
                             'code': '`\x005T\x15`\tW\x00[` 5`\x005U',
                             'storage': {
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=1170859069862169782511871033392474246841492526721L, 
                                balance=23L, 
                                code='`\x005T\x15`\tW\x00[` 5`\x005U', 
                                storage={
                                        }
                                )           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=100000000000000000000000L, 
                                code='0\xff', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069862169782511871033392474246841492526721L
        price = 100000000000000L
        data = ''
        caller = 1170859069862169782511871033392474246841492526721L
        value = 100000L        
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

    @unittest.skip('Gas or performance related')
    def test_ABAcalls2(self):
        header ={
                   'coinbase': 244687034288125203496486448490407391986876152250L,
                   'difficulty': 256L,
                   'gaslimit': 10000000L,
                   'number': 0L,
                   'timestamp': 1L
                  }
        pos_world = None

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=846782024548323446991784721256445173708587954613L, 
                                balance=0L, 
                                code='`\x01`\x00T\x01`\x00U`\x00`\x00`\x00`\x00`\x00s\x0fW.'\
                                     'R\x95\xc5\x7f\x15\x88o\x9b&>/m-l{^\xc6a\x03\xe8Z\x03\xf1', 
                                storage={
                                        }
                                )           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=100000000000000000000000L, 
                                code='`\x01`\x00T\x01`\x00U`\x00`\x00`\x00`\x00`\x01s\x94S\x04'\
                                     '\xeb\x96\x06[*\x98\xb5zH\xa0j\xe2\x8d(Zq\xb5a\x03\xe8Z\x03\xf1', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069862169782511871033392474246841492526721L
        price = 100000000000000L
        data = ''
        caller = 1170859069862169782511871033392474246841492526721L
        value = 100000L        
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

    @unittest.skip('Gas or performance related')
    def test_ABAcalls3(self):
        header ={
                   'coinbase': 244687034288125203496486448490407391986876152250L,
                   'difficulty': 256L,
                   'gaslimit': 10000000L,
                   'number': 0L,
                   'timestamp': 1L
                  }
        pos_world = None

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=846782024548323446991784721256445173708587954613L, 
                                balance=0L, 
                                code='`\x01`\x00T\x01`\x00U`\x00`\x00`\x00`\x00`\x00s\x0fW.'\
                                     'R\x95\xc5\x7f\x15\x88o\x9b&>/m-l{^\xc6a\x03\xe8Z\x03\xf1', 
                                storage={
                                        }
                                )           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=1025000L, 
                                code='`\x01`\x00T\x01`\x00U`\x00`\x00`\x00`\x00`\x01s\x94S\x04'\
                                     '\xeb\x96\x06[*\x98\xb5zH\xa0j\xe2\x8d(Zq\xb5a\x03\xe8Z\x03\xf1', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069862169782511871033392474246841492526721L
        price = 100000000000000L
        data = ''
        caller = 1170859069862169782511871033392474246841492526721L
        value = 100000L        
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

    @unittest.skip('Gas or performance related')
    def test_ABAcalls0(self):
        header ={
                   'coinbase': 244687034288125203496486448490407391986876152250L,
                   'difficulty': 256L,
                   'gaslimit': 10000000L,
                   'number': 0L,
                   'timestamp': 1L
                  }
        pos_world = {
                            846782024548323446991784721256445173708587954613L: {
                             'nonce': 0L,
                             'balance': 23L,
                             'code': '`\x00`\x00`\x00`\x00`\x17s\x0fW.R\x95\xc5\x7f\x15\x88o\x9b&>/m-l{^\xc6a\x01\xf4\xf1`\x01\x01XU',
                             'storage': {
                             }
                            },
                            87579061662017136990230301793909925042452127430L: {
                             'nonce': 0L,
                             'balance': 100000000000000000000000L,
                             'code': '`\x00`\x00`\x00`\x00`\x18s\x94S\x04\xeb\x96\x06[*\x98\xb5zH\xa0j\xe2\x8d(Zq\xb5a\x03\xe8\xf1XU',
                             'storage': {
                              35L: 1L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=846782024548323446991784721256445173708587954613L, 
                                balance=23L, 
                                code='`\x00`\x00`\x00`\x00`\x17s\x0fW.R\x95\xc5\x7f\x15\x88o\x9b&'\
                                     '>/m-l{^\xc6a\x01\xf4\xf1`\x01\x01XU', 
                                storage={
                                        }
                                )           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=100000000000000000000000L, 
                                code='`\x00`\x00`\x00`\x00`\x18s\x94S\x04\xeb\x96\x06[*\x98\xb5zH'\
                                     '\xa0j\xe2\x8d(Zq\xb5a\x03\xe8\xf1XU', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069862169782511871033392474246841492526721L
        price = 100000000000000L
        data = ''
        caller = 1170859069862169782511871033392474246841492526721L
        value = 100000L        
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

    @unittest.skip('Gas or performance related')
    def test_ABAcalls1(self):
        header ={
                   'coinbase': 244687034288125203496486448490407391986876152250L,
                   'difficulty': 256L,
                   'gaslimit': 10000000L,
                   'number': 0L,
                   'timestamp': 1L
                  }
        pos_world = None

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=846782024548323446991784721256445173708587954613L, 
                                balance=23L, 
                                code='`\x00`\x00`\x00`\x00`\x17s\x0fW.R\x95\xc5\x7f\x15\x88o\x9b&'\
                                     '>/m-l{^\xc6a\x03\xe8Z\x03\xf1`\x01\x01XU', 
                                storage={
                                        }
                                )           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=100000000000000000000000L, 
                                code='`\x00`\x00`\x00`\x00`\x18s\x94S\x04\xeb\x96\x06[*\x98\xb5zH'\
                                     '\xa0j\xe2\x8d(Zq\xb5a\x03\xe8Z\x03\xf1XU', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069862169782511871033392474246841492526721L
        price = 100000000000000L
        data = ''
        caller = 1170859069862169782511871033392474246841492526721L
        value = 100000L        
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

    def test_TestNameRegistrator(self):
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
                             'code': '`\x005T\x15`\tW\x00[` 5`\x005U',
                             'storage': {
                              115792089237316195423570985008687907853269984665640564039457584007913129639930L: 115792089237316195423570985008687907853269984665640564039457584007913129639930L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=100000000000000000000000L, 
                                code='`\x005T\x15`\tW\x00[` 5`\x005U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069862169782511871033392474246841492526721L
        price = 100000000000000L
        data = '\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xfa\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xfa'
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

    def test_return1(self):
        header ={
                   'coinbase': 244687034288125203496486448490407391986876152250L,
                   'difficulty': 256L,
                   'gaslimit': 10000000L,
                   'number': 0L,
                   'timestamp': 1L
                  }
        pos_world = {
                            1170859069862169782511871033392474246841492526721L: {
                             'nonce': 0L,
                             'balance': 23L,
                             'code': '`7`\x00S`\x00Q`\x00U`\x02`\x00\xf3',
                             'storage': {
                              0L: 24877206672079651360532828810460292702850973268008714930352215314200086446080L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=1170859069862169782511871033392474246841492526721L, 
                                balance=23L, 
                                code='`7`\x00S`\x00Q`\x00U`\x02`\x00\xf3', 
                                storage={
                                        }
                                )        
        address = 1170859069862169782511871033392474246841492526721L
        origin = 87579061662017136990230301793909925042452127430L
        price = 100000000000000L
        data = '\xaa'
        caller = 87579061662017136990230301793909925042452127430L
        value = 23L        
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

    def test_return0(self):
        header ={
                   'coinbase': 244687034288125203496486448490407391986876152250L,
                   'difficulty': 256L,
                   'gaslimit': 10000000L,
                   'number': 0L,
                   'timestamp': 1L
                  }
        pos_world = {
                            1170859069862169782511871033392474246841492526721L: {
                             'nonce': 0L,
                             'balance': 23L,
                             'code': '`7`\x00S`\x00Q`\x00U`\x01`\x00\xf3',
                             'storage': {
                              0L: 24877206672079651360532828810460292702850973268008714930352215314200086446080L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=1170859069862169782511871033392474246841492526721L, 
                                balance=23L, 
                                code='`7`\x00S`\x00Q`\x00U`\x01`\x00\xf3', 
                                storage={
                                        }
                                )        
        address = 1170859069862169782511871033392474246841492526721L
        origin = 87579061662017136990230301793909925042452127430L
        price = 100000000000000L
        data = '\xaa'
        caller = 87579061662017136990230301793909925042452127430L
        value = 23L        
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

    def test_return2(self):
        header ={
                   'coinbase': 244687034288125203496486448490407391986876152250L,
                   'difficulty': 256L,
                   'gaslimit': 10000000L,
                   'number': 0L,
                   'timestamp': 1L
                  }
        pos_world = {
                            1170859069862169782511871033392474246841492526721L: {
                             'nonce': 0L,
                             'balance': 23L,
                             'code': '`7`\x00S`\x00Q`\x00U`!`\x00\xf3',
                             'storage': {
                              0L: 24877206672079651360532828810460292702850973268008714930352215314200086446080L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=1170859069862169782511871033392474246841492526721L, 
                                balance=23L, 
                                code='`7`\x00S`\x00Q`\x00U`!`\x00\xf3', 
                                storage={
                                        }
                                )        
        address = 1170859069862169782511871033392474246841492526721L
        origin = 87579061662017136990230301793909925042452127430L
        price = 100000000000000L
        data = '\xaa'
        caller = 87579061662017136990230301793909925042452127430L
        value = 23L        
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

    def test_CallRecursiveBomb2(self):
        header ={
                   'coinbase': 244687034288125203496486448490407391986876152250L,
                   'difficulty': 256L,
                   'gaslimit': 10000000L,
                   'number': 0L,
                   'timestamp': 1L
                  }
        pos_world = {
                            87579061662017136990230301793909925042452127430L: {
                             'nonce': 0L,
                             'balance': 20000000L,
                             'code': '`\x01`\x00T\x01`\x00U`\x00`\x00`\x00`\x00`\x000`\xe0Z\x03\xf1`\x01U',
                             'storage': {
                              0L: 1L,
                              1L: 1L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=20000000L, 
                                code='`\x01`\x00T\x01`\x00U`\x00`\x00`\x00`\x00`\x000`\xe0Z'\
                                     '\x03\xf1`\x01U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069862169782511871033392474246841492526721L
        price = 1L
        data = ''
        caller = 1170859069862169782511871033392474246841492526721L
        value = 100000L        
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

    def test_CallRecursiveBomb3(self):
        header ={
                   'coinbase': 244687034288125203496486448490407391986876152250L,
                   'difficulty': 256L,
                   'gaslimit': 10000000L,
                   'number': 0L,
                   'timestamp': 1L
                  }
        pos_world = {
                            87579061662017136990230301793909925042452127430L: {
                             'nonce': 0L,
                             'balance': 20000000L,
                             'code': '`\x01`\x00T\x01`\x00U`\x00`\x00`\x00`\x00`\x000`\xe0Z\x03\xf1`\x01U',
                             'storage': {
                              0L: 1L,
                              1L: 1L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=20000000L, 
                                code='`\x01`\x00T\x01`\x00U`\x00`\x00`\x00`\x00`\x000`\xe0Z'\
                                     '\x03\xf1`\x01U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069862169782511871033392474246841492526721L
        price = 1L
        data = ''
        caller = 1170859069862169782511871033392474246841492526721L
        value = 100000L        
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

    def test_CallRecursiveBomb0(self):
        header ={
                   'coinbase': 244687034288125203496486448490407391986876152250L,
                   'difficulty': 256L,
                   'gaslimit': 10000000L,
                   'number': 0L,
                   'timestamp': 1L
                  }
        pos_world = {
                            846782024548323446991784721256445173708587954613L: {
                             'nonce': 0L,
                             'balance': 100000000000000000000000L,
                             'code': '`\x01`\x00T\x01`\x00U`\x00`\x00`\x00`\x00`\x000`\xe0Z\x03\xf1`\x01U',
                             'storage': {
                             }
                            },
                            87579061662017136990230301793909925042452127430L: {
                             'nonce': 0L,
                             'balance': 20000000L,
                             'code': '`\x00`\x00`\x00`\x00`\x17s\x94S\x04\xeb\x96\x06[*\x98\xb5zH\xa0j\xe2\x8d(Zq\xb5b\x01\x86\xa0\xf1',
                             'storage': {
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=846782024548323446991784721256445173708587954613L, 
                                balance=100000000000000000000000L, 
                                code='`\x01`\x00T\x01`\x00U`\x00`\x00`\x00`\x00`\x000`\xe0Z'\
                                     '\x03\xf1`\x01U', 
                                storage={
                                        }
                                )           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=20000000L, 
                                code='`\x00`\x00`\x00`\x00`\x17s\x94S\x04\xeb\x96\x06[*\x98\xb5zH'\
                                     '\xa0j\xe2\x8d(Zq\xb5b\x01\x86\xa0\xf1', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069862169782511871033392474246841492526721L
        price = 1L
        data = ''
        caller = 1170859069862169782511871033392474246841492526721L
        value = 100000L        
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

    def test_CallRecursiveBomb1(self):
        header ={
                   'coinbase': 244687034288125203496486448490407391986876152250L,
                   'difficulty': 256L,
                   'gaslimit': 10000000L,
                   'number': 0L,
                   'timestamp': 1L
                  }
        pos_world = {
                            87579061662017136990230301793909925042452127430L: {
                             'nonce': 0L,
                             'balance': 20000000L,
                             'code': '`\x01`\x00T\x01`\x00U`\x00`\x00`\x00`\x00`\x000`\xe0Z\x03\xf1`\x01U',
                             'storage': {
                              0L: 1L,
                              1L: 1L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=20000000L, 
                                code='`\x01`\x00T\x01`\x00U`\x00`\x00`\x00`\x00`\x000`\xe0Z'\
                                     '\x03\xf1`\x01U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069862169782511871033392474246841492526721L
        price = 1L
        data = ''
        caller = 1170859069862169782511871033392474246841492526721L
        value = 100000L        
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

    def test_CallToPrecompiledContract(self):
        header ={
                   'coinbase': 244687034288125203496486448490407391986876152250L,
                   'difficulty': 115792089237316195423570985008687907853269984665640564039457584007913129639935L,
                   'gaslimit': 1000000L,
                   'number': 0L,
                   'timestamp': 2L
                  }
        pos_world = {
                            87579061662017136990230301793909925042452127430L: {
                             'nonce': 0L,
                             'balance': 100000000000000000000000L,
                             'code': 'BCCBBCBC\xf1EU',
                             'storage': {
                              1000000L: 1L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=100000000000000000000000L, 
                                code='BCCBBCBC\xf1EU', 
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

    def test_createNameRegistrator(self):
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
                             'code': '|`\x10\x80`\x0c`\x009`\x00\xf3\x00`\x005T\x15`\tW\x00[` 5`\x005U`\x00R`\x1d`\x03`\x17\xf0`\x00U',
                             'storage': {
                              0L: 846782024548323446991784721256445173708587954613L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=100000000000000000000000L, 
                                code='|`\x10\x80`\x0c`\x009`\x00\xf3\x00`\x005T\x15`\tW\x00['\
                                     '` 5`\x005U`\x00R`\x1d`\x03`\x17\xf0`\x00U', 
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
