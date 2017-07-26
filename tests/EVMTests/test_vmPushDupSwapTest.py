
import struct
import unittest
import json
from manticore.platforms import evm
from manticore.core import state
from manticore.core.smtlib import Operators, ConstraintSet
import os


class EVMTest_vmPushDupSwapTest(unittest.TestCase):
    _multiprocess_can_split_ = True
    maxDiff=None 

    def test_swap10(self):
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
                             'code': '`\n`\t`\x08`\x07`\x06`\x05`\x04`\x03`\x02`\x01`\x03\x99U',
                             'storage': {
                              10L: 1L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=100000000000000000000000L, 
                                code='`\n`\t`\x08`\x07`\x06`\x05`\x04`\x03`\x02`\x01`\x03\x99'\
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

    def test_swap11(self):
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
                             'code': '`\x0b`\n`\t`\x08`\x07`\x06`\x05`\x04`\x03`\x02`\x01`\x03\x9aU',
                             'storage': {
                              11L: 1L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=100000000000000000000000L, 
                                code='`\x0b`\n`\t`\x08`\x07`\x06`\x05`\x04`\x03`\x02`\x01`'\
                                     '\x03\x9aU', 
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

    def test_swap12(self):
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
                             'code': '`\x0c`\x0b`\n`\t`\x08`\x07`\x06`\x05`\x04`\x03`\x02`\x01`\x03\x9bU',
                             'storage': {
                              12L: 1L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=100000000000000000000000L, 
                                code='`\x0c`\x0b`\n`\t`\x08`\x07`\x06`\x05`\x04`\x03`\x02`'\
                                     '\x01`\x03\x9bU', 
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

    def test_swap13(self):
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
                             'code': '`\r`\x0c`\x0b`\n`\t`\x08`\x07`\x06`\x05`\x04`\x03`\x02`\x01`\x03\x9cU',
                             'storage': {
                              13L: 1L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=100000000000000000000000L, 
                                code='`\r`\x0c`\x0b`\n`\t`\x08`\x07`\x06`\x05`\x04`\x03`'\
                                     '\x02`\x01`\x03\x9cU', 
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

    def test_swap14(self):
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
                             'code': '`\x0e`\r`\x0c`\x0b`\n`\t`\x08`\x07`\x06`\x05`\x04`\x03`\x02`\x01`\x03\x9dU',
                             'storage': {
                              14L: 1L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=100000000000000000000000L, 
                                code='`\x0e`\r`\x0c`\x0b`\n`\t`\x08`\x07`\x06`\x05`\x04`'\
                                     '\x03`\x02`\x01`\x03\x9dU', 
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

    def test_swap15(self):
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
                             'code': '`\x0f`\x0e`\r`\x0c`\x0b`\n`\t`\x08`\x07`\x06`\x05`\x04`\x03`\x02`\x01`\x03\x9eU',
                             'storage': {
                              15L: 1L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=100000000000000000000000L, 
                                code='`\x0f`\x0e`\r`\x0c`\x0b`\n`\t`\x08`\x07`\x06`\x05`'\
                                     '\x04`\x03`\x02`\x01`\x03\x9eU', 
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

    def test_swap16(self):
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
                             'code': '`\x10`\x0f`\x0e`\r`\x0c`\x0b`\n`\t`\x08`\x07`\x06`\x05`\x04`\x03`\x02`\x01`\x03\x9fU',
                             'storage': {
                              16L: 1L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=100000000000000000000000L, 
                                code='`\x10`\x0f`\x0e`\r`\x0c`\x0b`\n`\t`\x08`\x07`\x06`'\
                                     '\x05`\x04`\x03`\x02`\x01`\x03\x9fU', 
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

    def test_push33(self):
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
                                code='`ea\x07\xd2b\x04\xa0\xc7c\x02i!\xf4d\x0b\xc5X\x8e\xb1e7-'\
                                     '\x0f\x1d\xcanf\x1b\xa1\xd9\x01\x96\x1cqg\x0cU\xf7\xbc#\x03\x8e8h\x05'\
                                     'k\xc7^-c\x0f\xff\xffi\x02\x1e\x19\xe0\xc9\xba\xb2@\x00\x01j\x08]\x1c'\
                                     'n\x80P\xf0\xea\x1cq\xbdk\x06\x88\xbe6T?<6\xe68\xe3zl\x03'\
                                     '\xd4\x1fs\xd5]\rH*\xe5UU7m\xc7h\x10\xd0\xfe\x03\xc9\x19d\xd3'\
                                     '\x1cq\xc6\xf4na]\xd06\x0c\x07\xd91f;\x14\xe3\x8e8\xb1o-\xa3'\
                                     "\xf9\x99U\xa3\xad\xcf'\xeb\xb1\xca\xaa\xaa\xaanp\x14\xcc\xbaj\x8b\xb1\xed5"\
                                     '\xbd\x86\xbf\x06\\q\xc7\x1c+q\tI\x1c]G\x81\xb7\x9c\x90\t\xdek\xfb'\
                                     '\x8e8\xe3\x8d\xe8r\x04\x14\xa0\xf6\xfd\xec\x810MLV>t\x0b\xff\xff\xff'\
                                     "\xff\xa5s\x11\x84'\xb3\xb4\xa0[\xc8\xa8\xa4\xde\x84Y\x86\x80\x00\x00\x00\x00\x01"\
                                     't\x06\xeb\x15\xe73\x1ery@\xd4\xacT\xb7\xcd\xca\x1cq\xc7\x1cq\xbdu'\
                                     '\x05g\xa9\x1c\x9f\xef\xc9n\xba\xa6&\xa2/\x98\xc5\xe68\xe3\x8e8\xe3zv'\
                                     '\x03*\xbd\x16\xc5\xb6\x80\x06\xe1]Z\xa3\x07\xe3\x83\xf4\xe5UUUUU7'\
                                     'w\x01\xa6B{\xdcO\rX\xea\xb5\xf4\x8a>\xc6\x7fd\xe2\x1cq\xc7\x1cq'\
                                     '\xc6\xf4x\x08\r\xd0\xa0\xc9\xb9\xff,*\x0ct\x0b\x06\x85:\n\x98\x0e\xe3\x8e'\
                                     '8\xe3\x8e8\xb1y\x03\xc6y\xcb^\x8f/\x9c\xb3\xb5\xd6e+\x0es4\xf7'\
                                     'F\xfa\xaa\xaa\xaa\xaa\xaa\xaanz\x01\xb8s\x81Y\x17\xeb\xb2\xbf;\x89\n\x1a'\
                                     '\xf4\x95\xd6#[\xae<q\xc7\x1cq\xc7\x1c+{\x07\xaeL\xca\x96\xe1\xa5]'\
                                     '\xfaI\xc8Z\xd3\xc3\xe6\x0eBk\x92\xfb\x8e8\xe3\x8e8\xe3\x8d\xe8|\x03`'\
                                     '\x18\xbf\x07N)+\xcc}l\x8b\xea\x0f\x96\x99D0F\x17\x8b\xff\xff\xff\xff'\
                                     '\xff\xff\xff\xa5}\x0e}4\xc6J\x9c\x85\xd4F\r\xbb\xca\x87\x19kaa\x8a'\
                                     'K\xd2\x16\x80\x00\x00\x00\x00\x00\x00\x00\x01~\x05\xb9\x01\xf4\x8a[\x99Mer'\
                                     'P+\xc4\xeaC', 
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

    def test_push32(self):
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
                             'code': '\x7f\x10\x11"3DUfw\x88\x99\xaa\xbb\xcc\xdd\xee\xff\x00\x11"3DUfw\x88\x99\xaa\xbb\xcc\xdd\xee\xff`\x03U',
                             'storage': {
                              3L: 7267278018962933114737518846705396307879025787387688620599141924857001668351L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=100000000000000000000000L, 
                                code='\x7f\x10\x11"3DUfw\x88\x99\xaa\xbb\xcc\xdd\xee\xff\x00\x11"3DU'\
                                     'fw\x88\x99\xaa\xbb\xcc\xdd\xee\xff`\x03U', 
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

    def test_push31(self):
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
                             'code': '~\x11"3DUfw\x88\x99\xaa\xbb\xcc\xdd\xee\xff\x00\x11"3DUfw\x88\x99\xaa\xbb\xcc\xdd\xee\xff`\x03U',
                             'storage': {
                              3L: 30272441630670900764332283662402067049651745785153368133042924362431065855L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=100000000000000000000000L, 
                                code='~\x11"3DUfw\x88\x99\xaa\xbb\xcc\xdd\xee\xff\x00\x11"3DUf'\
                                     'w\x88\x99\xaa\xbb\xcc\xdd\xee\xff`\x03U', 
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

    def test_push30(self):
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
                             'code': '}"3DUfw\x88\x99\xaa\xbb\xcc\xdd\xee\xff\x00\x11"3DUfw\x88\x99\xaa\xbb\xcc\xdd\xee\xff`\x03U',
                             'storage': {
                              3L: 236041529438367161416226149772452280584519538267845844975618940456529663L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=100000000000000000000000L, 
                                code='}"3DUfw\x88\x99\xaa\xbb\xcc\xdd\xee\xff\x00\x11"3DUfw'\
                                     '\x88\x99\xaa\xbb\xcc\xdd\xee\xff`\x03U', 
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

    def test_push32Undefined3(self):
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
                             'code': '\x7f',
                             'storage': {
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=100000000000000000000000L, 
                                code='\x7f', 
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

    def test_push32Undefined2(self):
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
                             'code': '\x7f\x01\x02\x03\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00`\x00U',
                             'storage': {
                              0L: 455867247951863528723853059459259808159848198720826202355039887506167300096L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=100000000000000000000000L, 
                                code='\x7f\x01\x02\x03\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00'\
                                     '\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00`\x00U', 
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

    def test_push32AndSuicide(self):
        header ={
                   'coinbase': 244687034288125203496486448490407391986876152250L,
                   'difficulty': 256L,
                   'gaslimit': 1000000L,
                   'number': 0L,
                   'timestamp': 1L
                  }
        pos_world = {
                            1072149959305905970786075080742599377868915793390L: {
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
                                code='\x7f\xff\x10\x11"3DUfw\x88\x99\xaa\xbb\xcc\xdd\xee\xff\x00\x11"3D'\
                                     'Ufw\x88\x99\xaa\xbb\xcc\xdd\xee\xff`\x03U', 
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

    def test_dup5(self):
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
                             'code': '`\x05`\x04`\x03`\x02`\x01\x84`\x03U',
                             'storage': {
                              3L: 5L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=100000000000000000000000L, 
                                code='`\x05`\x04`\x03`\x02`\x01\x84`\x03U', 
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

    def test_dup4(self):
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
                             'code': '`\x04`\x03`\x02`\x01\x83`\x03U',
                             'storage': {
                              3L: 4L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=100000000000000000000000L, 
                                code='`\x04`\x03`\x02`\x01\x83`\x03U', 
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

    def test_dup7(self):
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
                             'code': '`\x07`\x06`\x05`\x04`\x03`\x02`\x01\x86`\x03U',
                             'storage': {
                              3L: 7L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=100000000000000000000000L, 
                                code='`\x07`\x06`\x05`\x04`\x03`\x02`\x01\x86`\x03U', 
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

    def test_dup6(self):
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
                             'code': '`\x06`\x05`\x04`\x03`\x02`\x01\x85`\x03U',
                             'storage': {
                              3L: 6L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=100000000000000000000000L, 
                                code='`\x06`\x05`\x04`\x03`\x02`\x01\x85`\x03U', 
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

    def test_dup1(self):
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
                             'code': '\x7f\x10\x11"3DUfw\x88\x99\xaa\xbb\xcc\xdd\xee\xff\x00\x11"3DUfw\x88\x99\xaa\xbb\xcc\xdd\xee\xff\x80`\x03U',
                             'storage': {
                              3L: 7267278018962933114737518846705396307879025787387688620599141924857001668351L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=100000000000000000000000L, 
                                code='\x7f\x10\x11"3DUfw\x88\x99\xaa\xbb\xcc\xdd\xee\xff\x00\x11"3DU'\
                                     'fw\x88\x99\xaa\xbb\xcc\xdd\xee\xff\x80`\x03U', 
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

    def test_dup3(self):
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
                             'code': '`\x03`\x02`\x01\x82`\x03U',
                             'storage': {
                              3L: 3L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=100000000000000000000000L, 
                                code='`\x03`\x02`\x01\x82`\x03U', 
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

    def test_dup2(self):
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
                             'code': '`\x02`\x01\x81`\x03U',
                             'storage': {
                              3L: 2L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=100000000000000000000000L, 
                                code='`\x02`\x01\x81`\x03U', 
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

    def test_dup9(self):
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
                             'code': '`\t`\x08`\x07`\x06`\x05`\x04`\x03`\x02`\x01\x88`\x03U',
                             'storage': {
                              3L: 9L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=100000000000000000000000L, 
                                code='`\t`\x08`\x07`\x06`\x05`\x04`\x03`\x02`\x01\x88`\x03U', 
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

    def test_dup8(self):
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
                             'code': '`\x08`\x07`\x06`\x05`\x04`\x03`\x02`\x01\x87`\x03U',
                             'storage': {
                              3L: 8L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=100000000000000000000000L, 
                                code='`\x08`\x07`\x06`\x05`\x04`\x03`\x02`\x01\x87`\x03U', 
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

    def test_push27(self):
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
                             'code': 'zUfw\x88\x99\xaa\xbb\xcc\xdd\xee\xff\x00\x11"3DUfw\x88\x99\xaa\xbb\xcc\xdd\xee\xff`\x03U',
                             'storage': {
                              3L: 35131629848125220974259712924447428653982015895563991539578171135L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=100000000000000000000000L, 
                                code='zUfw\x88\x99\xaa\xbb\xcc\xdd\xee\xff\x00\x11"3DUfw\x88\x99\xaa'\
                                     '\xbb\xcc\xdd\xee\xff`\x03U', 
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

    def test_push32FillUpInputWithZerosAtTheEnd(self):
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
                             'code': '\x7f\xff\x10\x11"3DUfw\x88\x99\xaa\xbb\xcc\xdd\xee\xff\x00\x11"3DUfw\x88\x99\xaa\xbb\xcc\xdd',
                             'storage': {
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=100000000000000000000000L, 
                                code='\x7f\xff\x10\x11"3DUfw\x88\x99\xaa\xbb\xcc\xdd\xee\xff\x00\x11"3D'\
                                     'Ufw\x88\x99\xaa\xbb\xcc\xdd', 
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

    def test_push20(self):
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
                             'code': 's\xcc\xdd\xee\xff\x00\x11"3DUfw\x88\x99\xaa\xbb\xcc\xdd\xee\xff`\x03U',
                             'storage': {
                              3L: 1169583401433082817146156952160516058783057571583L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=100000000000000000000000L, 
                                code='s\xcc\xdd\xee\xff\x00\x11"3DUfw\x88\x99\xaa\xbb\xcc\xdd\xee\xff`\x03'\
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

    def test_push21(self):
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
                             'code': 't\xbb\xcc\xdd\xee\xff\x00\x11"3DUfw\x88\x99\xaa\xbb\xcc\xdd\xee\xff`\x03U',
                             'storage': {
                              3L: 274470389582311928521235220670105440734442443108095L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=100000000000000000000000L, 
                                code='t\xbb\xcc\xdd\xee\xff\x00\x11"3DUfw\x88\x99\xaa\xbb\xcc\xdd\xee\xff`'\
                                     '\x03U', 
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

    def test_dup2error(self):
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
                                code='\x7f\x10\x11"3DUfw\x88\x99\xaa\xbb\xcc\xdd\xee\xff\x00\x11"3DU'\
                                     'fw\x88\x99\xaa\xbb\xcc\xdd\xee\xff\x81`\x03U', 
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

    def test_dup16(self):
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
                             'code': '`\x10`\x0f`\x0e`\r`\x0c`\x0b`\n`\t`\x08`\x07`\x06`\x05`\x04`\x03`\x02`\x01\x8f`\x03U',
                             'storage': {
                              3L: 16L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=100000000000000000000000L, 
                                code='`\x10`\x0f`\x0e`\r`\x0c`\x0b`\n`\t`\x08`\x07`\x06`'\
                                     '\x05`\x04`\x03`\x02`\x01\x8f`\x03U', 
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

    def test_swap1(self):
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
                             'code': '\x7f\x10\x11"3DUfw\x88\x99\xaa\xbb\xcc\xdd\xee\xff\x00\x11"3DUfw\x88\x99\xaa\xbb\xcc\xdd\xee\xff`\x03\x90U',
                             'storage': {
                              7267278018962933114737518846705396307879025787387688620599141924857001668351L: 3L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=100000000000000000000000L, 
                                code='\x7f\x10\x11"3DUfw\x88\x99\xaa\xbb\xcc\xdd\xee\xff\x00\x11"3DU'\
                                     'fw\x88\x99\xaa\xbb\xcc\xdd\xee\xff`\x03\x90U', 
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

    def test_push6(self):
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
                             'code': 'e\xaa\xbb\xcc\xdd\xee\xff`\x03U',
                             'storage': {
                              3L: 187723572702975L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=100000000000000000000000L, 
                                code='e\xaa\xbb\xcc\xdd\xee\xff`\x03U', 
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

    def test_push19(self):
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
                             'code': 'r\xdd\xee\xff\x00\x11"3DUfw\x88\x99\xaa\xbb\xcc\xdd\xee\xff`\x03U',
                             'storage': {
                              3L: 4949284185019554202595601089728027494736326399L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=100000000000000000000000L, 
                                code='r\xdd\xee\xff\x00\x11"3DUfw\x88\x99\xaa\xbb\xcc\xdd\xee\xff`\x03U', 
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

    def test_push18(self):
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
                             'code': 'q\xee\xff\x00\x11"3DUfw\x88\x99\xaa\xbb\xcc\xdd\xee\xff`\x03U',
                             'storage': {
                              3L: 20819496144286488316207351472739601914654463L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=100000000000000000000000L, 
                                code='q\xee\xff\x00\x11"3DUfw\x88\x99\xaa\xbb\xcc\xdd\xee\xff`\x03U', 
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

    def test_push25(self):
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
                             'code': 'xw\x88\x99\xaa\xbb\xcc\xdd\xee\xff\x00\x11"3DUfw\x88\x99\xaa\xbb\xcc\xdd\xee\xff`\x03U',
                             'storage': {
                              3L: 750324535175570361337661684931837641614045484574574219489023L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=100000000000000000000000L, 
                                code='xw\x88\x99\xaa\xbb\xcc\xdd\xee\xff\x00\x11"3DUfw\x88\x99\xaa\xbb\xcc'\
                                     '\xdd\xee\xff`\x03U', 
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

    def test_push11(self):
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
                             'code': 'jUfw\x88\x99\xaa\xbb\xcc\xdd\xee\xff`\x03U',
                             'storage': {
                              3L: 103242581054127139266096895L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=100000000000000000000000L, 
                                code='jUfw\x88\x99\xaa\xbb\xcc\xdd\xee\xff`\x03U', 
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

    def test_push10(self):
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
                             'code': 'ifw\x88\x99\xaa\xbb\xcc\xdd\xee\xff`\x03U',
                             'storage': {
                              3L: 483886386883659416071935L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=100000000000000000000000L, 
                                code='ifw\x88\x99\xaa\xbb\xcc\xdd\xee\xff`\x03U', 
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

    def test_push13(self):
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
                             'code': 'l3DUfw\x88\x99\xaa\xbb\xcc\xdd\xee\xff`\x03U',
                             'storage': {
                              3L: 4061784511476386809083292675839L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=100000000000000000000000L, 
                                code='l3DUfw\x88\x99\xaa\xbb\xcc\xdd\xee\xff`\x03U', 
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

    def test_push12(self):
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
                             'code': 'kDUfw\x88\x99\xaa\xbb\xcc\xdd\xee\xff`\x03U',
                             'storage': {
                              3L: 21148223248905591812551208703L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=100000000000000000000000L, 
                                code='kDUfw\x88\x99\xaa\xbb\xcc\xdd\xee\xff`\x03U', 
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

    def test_push15(self):
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
                             'code': 'n\x11"3DUfw\x88\x99\xaa\xbb\xcc\xdd\xee\xff`\x03U',
                             'storage': {
                              3L: 88962710306127702866241727433142015L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=100000000000000000000000L, 
                                code='n\x11"3DUfw\x88\x99\xaa\xbb\xcc\xdd\xee\xff`\x03U', 
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

    def test_push14(self):
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
                             'code': 'm"3DUfw\x88\x99\xaa\xbb\xcc\xdd\xee\xff`\x03U',
                             'storage': {
                              3L: 693663711035633181223289836400383L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=100000000000000000000000L, 
                                code='m"3DUfw\x88\x99\xaa\xbb\xcc\xdd\xee\xff`\x03U', 
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

    def test_push17(self):
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
                             'code': 'p\xff\x00\x11"3DUfw\x88\x99\xaa\xbb\xcc\xdd\xee\xff`\x03U',
                             'storage': {
                              3L: 86772092527549614310863391136828327063295L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=100000000000000000000000L, 
                                code='p\xff\x00\x11"3DUfw\x88\x99\xaa\xbb\xcc\xdd\xee\xff`\x03U', 
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

    def test_push16(self):
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
                             'code': 'o\x10\x11"3DUfw\x88\x99\xaa\xbb\xcc\xdd\xee\xff`\x03U',
                             'storage': {
                              3L: 21356610642864781669327154691918655231L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=100000000000000000000000L, 
                                code='o\x10\x11"3DUfw\x88\x99\xaa\xbb\xcc\xdd\xee\xff`\x03U', 
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

    def test_push1(self):
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
                             'code': '`\xff`\x03U',
                             'storage': {
                              3L: 255L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=100000000000000000000000L, 
                                code='`\xff`\x03U', 
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

    def test_push3(self):
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
                             'code': 'b\xdd\xee\xff`\x03U',
                             'storage': {
                              3L: 14544639L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=100000000000000000000000L, 
                                code='b\xdd\xee\xff`\x03U', 
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

    def test_push2(self):
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
                             'code': 'a\xee\xff`\x03U',
                             'storage': {
                              3L: 61183L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=100000000000000000000000L, 
                                code='a\xee\xff`\x03U', 
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

    def test_push5(self):
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
                             'code': 'd\xbb\xcc\xdd\xee\xff`\x03U',
                             'storage': {
                              3L: 806595981055L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=100000000000000000000000L, 
                                code='d\xbb\xcc\xdd\xee\xff`\x03U', 
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

    def test_push4(self):
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
                             'code': 'c\xcc\xdd\xee\xff`\x03U',
                             'storage': {
                              3L: 3437096703L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=100000000000000000000000L, 
                                code='c\xcc\xdd\xee\xff`\x03U', 
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

    def test_push7(self):
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
                             'code': 'f\x99\xaa\xbb\xcc\xdd\xee\xff`\x03U',
                             'storage': {
                              3L: 43253395009433343L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=100000000000000000000000L, 
                                code='f\x99\xaa\xbb\xcc\xdd\xee\xff`\x03U', 
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

    def test_swapjump1(self):
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
                                code='`\x05`\x02`\x01`\x0cWPP\x00', 
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

    def test_push9(self):
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
                             'code': 'hw\x88\x99\xaa\xbb\xcc\xdd\xee\xff`\x03U',
                             'storage': {
                              3L: 2205005630955604274943L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=100000000000000000000000L, 
                                code='hw\x88\x99\xaa\xbb\xcc\xdd\xee\xff`\x03U', 
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

    def test_push8(self):
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
                             'code': 'g\x88\x99\xaa\xbb\xcc\xdd\xee\xff`\x03U',
                             'storage': {
                              3L: 9843086184167632639L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=100000000000000000000000L, 
                                code='g\x88\x99\xaa\xbb\xcc\xdd\xee\xff`\x03U', 
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

    def test_swap6(self):
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
                             'code': '`\x06`\x05`\x04`\x03`\x02`\x01`\x03\x95U',
                             'storage': {
                              6L: 1L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=100000000000000000000000L, 
                                code='`\x06`\x05`\x04`\x03`\x02`\x01`\x03\x95U', 
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

    def test_push1_missingStack(self):
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
                             'code': '`',
                             'storage': {
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=100000000000000000000000L, 
                                code='`', 
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

    def test_push24(self):
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
                             'code': 'w\x88\x99\xaa\xbb\xcc\xdd\xee\xff\x00\x11"3DUfw\x88\x99\xaa\xbb\xcc\xdd\xee\xff`\x03U',
                             'storage': {
                              3L: 3349428664555350441202743570125338097865186683354112454399L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=100000000000000000000000L, 
                                code='w\x88\x99\xaa\xbb\xcc\xdd\xee\xff\x00\x11"3DUfw\x88\x99\xaa\xbb\xcc\xdd'\
                                     '\xee\xff`\x03U', 
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

    def test_swap7(self):
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
                             'code': '`\x07`\x06`\x05`\x04`\x03`\x02`\x01`\x03\x96U',
                             'storage': {
                              7L: 1L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=100000000000000000000000L, 
                                code='`\x07`\x06`\x05`\x04`\x03`\x02`\x01`\x03\x96U', 
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

    def test_push26(self):
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
                             'code': 'yfw\x88\x99\xaa\xbb\xcc\xdd\xee\xff\x00\x11"3DUfw\x88\x99\xaa\xbb\xcc\xdd\xee\xff`\x03U',
                             'storage': {
                              3L: 164658005049592578466617795103730423098878750850419443420229375L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=100000000000000000000000L, 
                                code='yfw\x88\x99\xaa\xbb\xcc\xdd\xee\xff\x00\x11"3DUfw\x88\x99\xaa\xbb'\
                                     '\xcc\xdd\xee\xff`\x03U', 
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

    def test_swap5(self):
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
                             'code': '`\x05`\x04`\x03`\x02`\x01`\x03\x94U',
                             'storage': {
                              5L: 1L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=100000000000000000000000L, 
                                code='`\x05`\x04`\x03`\x02`\x01`\x03\x94U', 
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

    def test_swap2(self):
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
                             'code': '`\x02`\x01`\x03\x91U',
                             'storage': {
                              2L: 1L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=100000000000000000000000L, 
                                code='`\x02`\x01`\x03\x91U', 
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

    def test_swap3(self):
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
                             'code': '`\x03`\x02`\x01`\x03\x92U',
                             'storage': {
                              3L: 1L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=100000000000000000000000L, 
                                code='`\x03`\x02`\x01`\x03\x92U', 
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

    def test_push22(self):
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
                             'code': 'u\xaa\xbb\xcc\xdd\xee\xff\x00\x11"3DUfw\x88\x99\xaa\xbb\xcc\xdd\xee\xff`\x03U',
                             'storage': {
                              3L: 63879021646223206928745599140482742456160626713423615L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=100000000000000000000000L, 
                                code='u\xaa\xbb\xcc\xdd\xee\xff\x00\x11"3DUfw\x88\x99\xaa\xbb\xcc\xdd\xee\xff'\
                                     '`\x03U', 
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

    def test_push23(self):
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
                             'code': 'v\x99\xaa\xbb\xcc\xdd\xee\xff\x00\x11"3DUfw\x88\x99\xaa\xbb\xcc\xdd\xee\xff`\x03U',
                             'storage': {
                              3L: 14718367631176285414980439046265314310810353482594119423L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=100000000000000000000000L, 
                                code='v\x99\xaa\xbb\xcc\xdd\xee\xff\x00\x11"3DUfw\x88\x99\xaa\xbb\xcc\xdd\xee'\
                                     '\xff`\x03U', 
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

    def test_push28(self):
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
                             'code': '{DUfw\x88\x99\xaa\xbb\xcc\xdd\xee\xff\x00\x11"3DUfw\x88\x99\xaa\xbb\xcc\xdd\xee\xff`\x03U',
                             'storage': {
                              3L: 7196367463310013916432685595414036826338848503132903556832724643583L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=100000000000000000000000L, 
                                code='{DUfw\x88\x99\xaa\xbb\xcc\xdd\xee\xff\x00\x11"3DUfw\x88\x99'\
                                     '\xaa\xbb\xcc\xdd\xee\xff`\x03U', 
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

    def test_push29(self):
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
                             'code': '|3DUfw\x88\x99\xaa\xbb\xcc\xdd\xee\xff\x00\x11"3DUfw\x88\x99\xaa\xbb\xcc\xdd\xee\xff`\x03U',
                             'storage': {
                              3L: 1382153647487992643444450455033415201181833214052702100093116847353599L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=100000000000000000000000L, 
                                code='|3DUfw\x88\x99\xaa\xbb\xcc\xdd\xee\xff\x00\x11"3DUfw\x88'\
                                     '\x99\xaa\xbb\xcc\xdd\xee\xff`\x03U', 
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

    def test_swap8(self):
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
                             'code': '`\x08`\x07`\x06`\x05`\x04`\x03`\x02`\x01`\x03\x97U',
                             'storage': {
                              8L: 1L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=100000000000000000000000L, 
                                code='`\x08`\x07`\x06`\x05`\x04`\x03`\x02`\x01`\x03\x97U', 
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

    def test_swap9(self):
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
                             'code': '`\t`\x08`\x07`\x06`\x05`\x04`\x03`\x02`\x01`\x03\x98U',
                             'storage': {
                              9L: 1L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=100000000000000000000000L, 
                                code='`\t`\x08`\x07`\x06`\x05`\x04`\x03`\x02`\x01`\x03\x98U', 
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

    def test_dup15(self):
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
                             'code': '`\x0f`\x0e`\r`\x0c`\x0b`\n`\t`\x08`\x07`\x06`\x05`\x04`\x03`\x02`\x01\x8e`\x03U',
                             'storage': {
                              3L: 15L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=100000000000000000000000L, 
                                code='`\x0f`\x0e`\r`\x0c`\x0b`\n`\t`\x08`\x07`\x06`\x05`'\
                                     '\x04`\x03`\x02`\x01\x8e`\x03U', 
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

    def test_dup14(self):
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
                             'code': '`\x0e`\r`\x0c`\x0b`\n`\t`\x08`\x07`\x06`\x05`\x04`\x03`\x02`\x01\x8d`\x03U',
                             'storage': {
                              3L: 14L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=100000000000000000000000L, 
                                code='`\x0e`\r`\x0c`\x0b`\n`\t`\x08`\x07`\x06`\x05`\x04`'\
                                     '\x03`\x02`\x01\x8d`\x03U', 
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

    def test_swap2error(self):
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
                                code='\x7f\x10\x11"3DUfw\x88\x99\xaa\xbb\xcc\xdd\xee\xff\x00\x11"3DU'\
                                     'fw\x88\x99\xaa\xbb\xcc\xdd\xee\xff`\x03\x91U', 
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

    def test_dup11(self):
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
                             'code': '`\x0b`\n`\t`\x08`\x07`\x06`\x05`\x04`\x03`\x02`\x01\x8a`\x03U',
                             'storage': {
                              3L: 11L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=100000000000000000000000L, 
                                code='`\x0b`\n`\t`\x08`\x07`\x06`\x05`\x04`\x03`\x02`\x01\x8a'\
                                     '`\x03U', 
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

    def test_dup10(self):
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
                             'code': '`\n`\t`\x08`\x07`\x06`\x05`\x04`\x03`\x02`\x01\x89`\x03U',
                             'storage': {
                              3L: 10L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=100000000000000000000000L, 
                                code='`\n`\t`\x08`\x07`\x06`\x05`\x04`\x03`\x02`\x01\x89`\x03'\
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

    def test_dup13(self):
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
                             'code': '`\r`\x0c`\x0b`\n`\t`\x08`\x07`\x06`\x05`\x04`\x03`\x02`\x01\x8c`\x03U',
                             'storage': {
                              3L: 13L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=100000000000000000000000L, 
                                code='`\r`\x0c`\x0b`\n`\t`\x08`\x07`\x06`\x05`\x04`\x03`'\
                                     '\x02`\x01\x8c`\x03U', 
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

    def test_dup12(self):
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
                             'code': '`\x0c`\x0b`\n`\t`\x08`\x07`\x06`\x05`\x04`\x03`\x02`\x01\x8b`\x03U',
                             'storage': {
                              3L: 12L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=100000000000000000000000L, 
                                code='`\x0c`\x0b`\n`\t`\x08`\x07`\x06`\x05`\x04`\x03`\x02`'\
                                     '\x01\x8b`\x03U', 
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

    def test_swap4(self):
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
                             'code': '`\x04`\x03`\x02`\x01`\x03\x93U',
                             'storage': {
                              4L: 1L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=100000000000000000000000L, 
                                code='`\x04`\x03`\x02`\x01`\x03\x93U', 
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

    def test_push32Undefined(self):
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
                             'code': '\x7f\x01\x02\x03`\x00U',
                             'storage': {
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=100000000000000000000000L, 
                                code='\x7f\x01\x02\x03`\x00U', 
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
