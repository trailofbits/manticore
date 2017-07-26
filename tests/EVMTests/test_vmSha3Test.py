
import struct
import unittest
import json
from manticore.platforms import evm
from manticore.core import state
from manticore.core.smtlib import Operators, ConstraintSet
import os


class EVMTest_vmSha3Test(unittest.TestCase):
    _multiprocess_can_split_ = True
    maxDiff=None 

    def test_sha3_memSizeQuadraticCost32(self):
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
                             'balance': 115792089237316195423570985008687907853269984665640564039457584007913129639935L,
                             'code': '`\x01a\x03\xe0 `\x00U',
                             'storage': {
                              0L: 85131057757245807317576516368191972321038229705283732634690444270750521936266L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=115792089237316195423570985008687907853269984665640564039457584007913129639935L, 
                                code='`\x01a\x03\xe0 `\x00U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069862169782511871033392474246841492526721L
        price = 1L
        data = ''
        caller = 1170859069862169782511871033392474246841492526721L
        value = 115792089237316195423570985008687907853269984665640564039457584007913129639935L        
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

    def test_sha3_memSizeQuadraticCost63(self):
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
                             'balance': 115792089237316195423570985008687907853269984665640564039457584007913129639935L,
                             'code': '`\x01a\x07\xc0 `\x00U',
                             'storage': {
                              0L: 85131057757245807317576516368191972321038229705283732634690444270750521936266L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=115792089237316195423570985008687907853269984665640564039457584007913129639935L, 
                                code='`\x01a\x07\xc0 `\x00U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069862169782511871033392474246841492526721L
        price = 1L
        data = ''
        caller = 1170859069862169782511871033392474246841492526721L
        value = 115792089237316195423570985008687907853269984665640564039457584007913129639935L        
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

    def test_sha3_bigOffset2(self):
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
                             'balance': 115792089237316195423570985008687907853269984665640564039457584007913129639935L,
                             'code': '`\x02c\x01\x00\x00\x00 `\x00U',
                             'storage': {
                              0L: 38292439343987868037672198288784556730787963328266909981497454499372014593944L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=115792089237316195423570985008687907853269984665640564039457584007913129639935L, 
                                code='`\x02c\x01\x00\x00\x00 `\x00U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069862169782511871033392474246841492526721L
        price = 1L
        data = ''
        caller = 1170859069862169782511871033392474246841492526721L
        value = 115792089237316195423570985008687907853269984665640564039457584007913129639935L        
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

    def test_sha3_memSizeQuadraticCost65(self):
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
                             'balance': 115792089237316195423570985008687907853269984665640564039457584007913129639935L,
                             'code': '`\x01a\x08\x00 `\x00U',
                             'storage': {
                              0L: 85131057757245807317576516368191972321038229705283732634690444270750521936266L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=115792089237316195423570985008687907853269984665640564039457584007913129639935L, 
                                code='`\x01a\x08\x00 `\x00U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069862169782511871033392474246841492526721L
        price = 1L
        data = ''
        caller = 1170859069862169782511871033392474246841492526721L
        value = 115792089237316195423570985008687907853269984665640564039457584007913129639935L        
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

    def test_sha3_memSizeNoQuadraticCost31(self):
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
                             'balance': 115792089237316195423570985008687907853269984665640564039457584007913129639935L,
                             'code': '`\x01a\x03\xc0 `\x00U',
                             'storage': {
                              0L: 85131057757245807317576516368191972321038229705283732634690444270750521936266L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=115792089237316195423570985008687907853269984665640564039457584007913129639935L, 
                                code='`\x01a\x03\xc0 `\x00U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069862169782511871033392474246841492526721L
        price = 1L
        data = ''
        caller = 1170859069862169782511871033392474246841492526721L
        value = 115792089237316195423570985008687907853269984665640564039457584007913129639935L        
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

    def test_sha3_memSizeQuadraticCost32_zeroSize(self):
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
                             'balance': 115792089237316195423570985008687907853269984665640564039457584007913129639935L,
                             'code': '`\x00a\x04\x00 `\x00U',
                             'storage': {
                              0L: 89477152217924674838424037953991966239322087453347756267410168184682657981552L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=115792089237316195423570985008687907853269984665640564039457584007913129639935L, 
                                code='`\x00a\x04\x00 `\x00U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069862169782511871033392474246841492526721L
        price = 1L
        data = ''
        caller = 1170859069862169782511871033392474246841492526721L
        value = 115792089237316195423570985008687907853269984665640564039457584007913129639935L        
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

    def test_sha3_6(self):
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
                                code='\x7f\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff'\
                                     '\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\x7f\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff'\
                                     '\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff `\x00'\
                                     'U', 
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

    def test_sha3_4(self):
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
                                code='`dd\x0f\xff\xff\xff\xff `\x00U', 
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

    def test_sha3_5(self):
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
                                code="d\x0f\xff\xff\xff\xffa'\x10 `\x00U", 
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

    def test_sha3_2(self):
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
                             'code': '`\n`\n `\x00U',
                             'storage': {
                              0L: 48770040874999722911352515349406742418672666995386952638548776145659901556231L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=100000000000000000000000L, 
                                code='`\n`\n `\x00U', 
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

    @unittest.skip('Gas or performance related')
    def test_sha3_3(self):
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
                                code='b\x0f\xff\xffa\x03\xe8 `\x00U', 
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

    def test_sha3_0(self):
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
                             'code': '`\x00`\x00 `\x00U',
                             'storage': {
                              0L: 89477152217924674838424037953991966239322087453347756267410168184682657981552L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=100000000000000000000000L, 
                                code='`\x00`\x00 `\x00U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069862169782511871033392474246841492526721L
        price = 1000000000L
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

    def test_sha3_1(self):
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
                             'code': '`\x05`\x04 `\x00U',
                             'storage': {
                              0L: 88691373886691830474546593511551865147992741123997168990340854445980345442540L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=100000000000000000000000L, 
                                code='`\x05`\x04 `\x00U', 
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

    def test_sha3_bigSize(self):
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
                                balance=115792089237316195423570985008687907853269984665640564039457584007913129639935L, 
                                code='~\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff'\
                                     '\xff\xff\xff\xff\xff\xff\xff\xff\xff~\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff'\
                                     '\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff `\x00U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069862169782511871033392474246841492526721L
        price = 1L
        data = ''
        caller = 1170859069862169782511871033392474246841492526721L
        value = 115792089237316195423570985008687907853269984665640564039457584007913129639935L        
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

    def test_sha3_memSizeQuadraticCost33(self):
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
                             'balance': 115792089237316195423570985008687907853269984665640564039457584007913129639935L,
                             'code': '`\x01a\x04\x00 `\x00U',
                             'storage': {
                              0L: 85131057757245807317576516368191972321038229705283732634690444270750521936266L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=115792089237316195423570985008687907853269984665640564039457584007913129639935L, 
                                code='`\x01a\x04\x00 `\x00U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069862169782511871033392474246841492526721L
        price = 1L
        data = ''
        caller = 1170859069862169782511871033392474246841492526721L
        value = 115792089237316195423570985008687907853269984665640564039457584007913129639935L        
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

    def test_sha3_bigOffset(self):
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
                                balance=115792089237316195423570985008687907853269984665640564039457584007913129639935L, 
                                code='`\x02~\x0f\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff'\
                                     '\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff `\x00U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069862169782511871033392474246841492526721L
        price = 1L
        data = ''
        caller = 1170859069862169782511871033392474246841492526721L
        value = 115792089237316195423570985008687907853269984665640564039457584007913129639935L        
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

    def test_sha3_memSizeQuadraticCost64(self):
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
                             'balance': 115792089237316195423570985008687907853269984665640564039457584007913129639935L,
                             'code': '`\x01a\x07\xe0 `\x00U',
                             'storage': {
                              0L: 85131057757245807317576516368191972321038229705283732634690444270750521936266L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=115792089237316195423570985008687907853269984665640564039457584007913129639935L, 
                                code='`\x01a\x07\xe0 `\x00U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069862169782511871033392474246841492526721L
        price = 1L
        data = ''
        caller = 1170859069862169782511871033392474246841492526721L
        value = 115792089237316195423570985008687907853269984665640564039457584007913129639935L        
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

    def test_sha3_memSizeQuadraticCost64_2(self):
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
                             'balance': 115792089237316195423570985008687907853269984665640564039457584007913129639935L,
                             'code': '` a\x07\xe0 `\x00U',
                             'storage': {
                              0L: 18569430475105882587588266137607568536673111973893317399460219858819262702947L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=115792089237316195423570985008687907853269984665640564039457584007913129639935L, 
                                code='` a\x07\xe0 `\x00U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069862169782511871033392474246841492526721L
        price = 1L
        data = ''
        caller = 1170859069862169782511871033392474246841492526721L
        value = 115792089237316195423570985008687907853269984665640564039457584007913129639935L        
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
