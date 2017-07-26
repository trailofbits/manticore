
import struct
import unittest
import json
from manticore.platforms import evm
from manticore.core import state
from manticore.core.smtlib import Operators, ConstraintSet
import os


class EVMTest_vmArithmeticTest(unittest.TestCase):
    _multiprocess_can_split_ = True
    maxDiff=None 

    def test_addmodDivByZero1(self):
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
                             'balance': 1000000000000000000L,
                             'code': '`\x00`\x01`\x00\x08`\x00U',
                             'storage': {
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=1000000000000000000L, 
                                code='`\x00`\x01`\x00\x08`\x00U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069521887415590932569929099639409724315265L
        price = 100000000000000L
        data = ''
        caller = 1170859069521887415590932569929099639409724315265L
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

    def test_sdivByZero0(self):
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
                             'balance': 1000000000000000000L,
                             'code': '`\x00`\x00\x03`\x03`\x00\x03\x05`\x00U',
                             'storage': {
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=1000000000000000000L, 
                                code='`\x00`\x00\x03`\x03`\x00\x03\x05`\x00U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069521887415590932569929099639409724315265L
        price = 100000000000000L
        data = ''
        caller = 1170859069521887415590932569929099639409724315265L
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

    def test_sdivByZero1(self):
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
                             'balance': 1000000000000000000L,
                             'code': '`\x00\x7f\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff`\x00\x03\x05`\x00U',
                             'storage': {
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=1000000000000000000L, 
                                code='`\x00\x7f\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff'\
                                     '\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff`\x00\x03\x05`\x00U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069521887415590932569929099639409724315265L
        price = 100000000000000L
        data = ''
        caller = 1170859069521887415590932569929099639409724315265L
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

    def test_sdivByZero2(self):
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
                             'balance': 1000000000000000000L,
                             'code': '`\x01`\x00\x7f\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xfc\xf9#\xbd\xff`\x00\x03\x05\x01`\x00U',
                             'storage': {
                              0L: 1L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=1000000000000000000L, 
                                code='`\x01`\x00\x7f\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff'\
                                     '\xff\xff\xff\xff\xff\xff\xff\xff\xff\xfc\xf9#\xbd\xff`\x00\x03\x05\x01`\x00U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069521887415590932569929099639409724315265L
        price = 100000000000000L
        data = ''
        caller = 1170859069521887415590932569929099639409724315265L
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

    def test_mod0(self):
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
                             'balance': 1000000000000000000L,
                             'code': '`\x03`\x02\x06`\x00U',
                             'storage': {
                              0L: 2L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=1000000000000000000L, 
                                code='`\x03`\x02\x06`\x00U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069521887415590932569929099639409724315265L
        price = 100000000000000L
        data = ''
        caller = 1170859069521887415590932569929099639409724315265L
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

    def test_mod1(self):
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
                             'balance': 1000000000000000000L,
                             'code': '`\x02\x7f\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\x06`\x00U',
                             'storage': {
                              0L: 1L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=1000000000000000000L, 
                                code='`\x02\x7f\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff'\
                                     '\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\x06`\x00U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069521887415590932569929099639409724315265L
        price = 100000000000000L
        data = ''
        caller = 1170859069521887415590932569929099639409724315265L
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

    def test_expPowerOf256_29(self):
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
                             'balance': 1000000000000000000L,
                             'code': '`\x1da\x01\x00\n`\x00U`\x1d`\xff\n`\x01U`\x1da\x01\x01\n`\x02U',
                             'storage': {
                              0L: 6901746346790563787434755862277025452451108972170386555162524223799296L,
                              1L: 6161198947895343982399660568426761903988167460346780717372894287109375L,
                              2L: 7727883682589755429839543181003123889866610449799515773033206399769857L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=1000000000000000000L, 
                                code='`\x1da\x01\x00\n`\x00U`\x1d`\xff\n`\x01U`\x1da\x01\x01\n'\
                                     '`\x02U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069521887415590932569929099639409724315265L
        price = 100000000000000L
        data = ''
        caller = 1170859069521887415590932569929099639409724315265L
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

    def test_expPowerOf256_28(self):
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
                             'balance': 1000000000000000000L,
                             'code': '`\x1ca\x01\x00\n`\x00U`\x1c`\xff\n`\x01U`\x1ca\x01\x01\n`\x02U',
                             'storage': {
                              0L: 26959946667150639794667015087019630673637144422540572481103610249216L,
                              1L: 24161564501550368558430041444810830996032029256261885166168212890625L,
                              2L: 30069586313578814902099389809350676614266966730737415459273176652801L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=1000000000000000000L, 
                                code='`\x1ca\x01\x00\n`\x00U`\x1c`\xff\n`\x01U`\x1ca\x01\x01\n'\
                                     '`\x02U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069521887415590932569929099639409724315265L
        price = 100000000000000L
        data = ''
        caller = 1170859069521887415590932569929099639409724315265L
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

    def test_mod4(self):
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
                             'balance': 1000000000000000000L,
                             'code': '`\x03`\x02`\x00\x03\x06`\x00U',
                             'storage': {
                              0L: 2L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=1000000000000000000L, 
                                code='`\x03`\x02`\x00\x03\x06`\x00U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069521887415590932569929099639409724315265L
        price = 100000000000000L
        data = ''
        caller = 1170859069521887415590932569929099639409724315265L
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

    def test_expPowerOf256_23(self):
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
                             'balance': 1000000000000000000L,
                             'code': '`\x17a\x01\x00\n`\x00U`\x17`\xff\n`\x01U`\x17a\x01\x01\n`\x02U',
                             'storage': {
                              0L: 24519928653854221733733552434404946937899825954937634816L,
                              1L: 22409086343932890693549885316479244931352138519287109375L,
                              2L: 26820189163684151285035147401442659727467946863138510593L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=1000000000000000000L, 
                                code='`\x17a\x01\x00\n`\x00U`\x17`\xff\n`\x01U`\x17a\x01\x01\n'\
                                     '`\x02U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069521887415590932569929099639409724315265L
        price = 100000000000000L
        data = ''
        caller = 1170859069521887415590932569929099639409724315265L
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

    def test_expPowerOf256_22(self):
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
                             'balance': 1000000000000000000L,
                             'code': '`\x16a\x01\x00\n`\x00U`\x16`\xff\n`\x01U`\x16a\x01\x01\n`\x02U',
                             'storage': {
                              0L: 95780971304118053647396689196894323976171195136475136L,
                              1L: 87878769976207414484509354182271548750400543212890625L,
                              2L: 104358712699160121731654270044523967811159326315714049L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=1000000000000000000L, 
                                code='`\x16a\x01\x00\n`\x00U`\x16`\xff\n`\x01U`\x16a\x01\x01\n'\
                                     '`\x02U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069521887415590932569929099639409724315265L
        price = 100000000000000L
        data = ''
        caller = 1170859069521887415590932569929099639409724315265L
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

    def test_expPowerOf256_21(self):
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
                             'balance': 1000000000000000000L,
                             'code': '`\x15a\x01\x00\n`\x00U`\x15`\xff\n`\x01U`\x15a\x01\x01\n`\x02U',
                             'storage': {
                              0L: 374144419156711147060143317175368453031918731001856L,
                              1L: 344622627357676135233370016401064897060394287109375L,
                              2L: 406065029957821485337176148033167189926689985664257L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=1000000000000000000L, 
                                code='`\x15a\x01\x00\n`\x00U`\x15`\xff\n`\x01U`\x15a\x01\x01\n'\
                                     '`\x02U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069521887415590932569929099639409724315265L
        price = 100000000000000L
        data = ''
        caller = 1170859069521887415590932569929099639409724315265L
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

    def test_expPowerOf256_20(self):
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
                             'balance': 1000000000000000000L,
                             'code': '`\x14a\x01\x00\n`\x00U`\x14`\xff\n`\x01U`\x14a\x01\x01\n`\x02U',
                             'storage': {
                              0L: 1461501637330902918203684832716283019655932542976L,
                              1L: 1351461283755592687189686338827705478668212890625L,
                              2L: 1580019571820317063568778786121273112555213952001L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=1000000000000000000L, 
                                code='`\x14a\x01\x00\n`\x00U`\x14`\xff\n`\x01U`\x14a\x01\x01\n'\
                                     '`\x02U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069521887415590932569929099639409724315265L
        price = 100000000000000L
        data = ''
        caller = 1170859069521887415590932569929099639409724315265L
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

    def test_expPowerOf256_27(self):
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
                             'balance': 1000000000000000000L,
                             'code': '`\x1ba\x01\x00\n`\x00U`\x1b`\xff\n`\x01U`\x1ba\x01\x01\n`\x02U',
                             'storage': {
                              0L: 105312291668557186697918027683670432318895095400549111254310977536L,
                              1L: 94751233339413210033058986058081690180517761789262294769287109375L,
                              2L: 117002281375793054093771944783465667759793644866682550425187457793L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=1000000000000000000L, 
                                code='`\x1ba\x01\x00\n`\x00U`\x1b`\xff\n`\x01U`\x1ba\x01\x01\n'\
                                     '`\x02U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069521887415590932569929099639409724315265L
        price = 100000000000000L
        data = ''
        caller = 1170859069521887415590932569929099639409724315265L
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

    def test_expPowerOf256_26(self):
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
                             'balance': 1000000000000000000L,
                             'code': '`\x1aa\x01\x00\n`\x00U`\x1a`\xff\n`\x01U`\x1aa\x01\x01\n`\x02U',
                             'storage': {
                              0L: 411376139330301510538742295639337626245683966408394965837152256L,
                              1L: 371573464076130235423760729639536039923599065840244293212890625L,
                              2L: 455261795236548848613898617834496761711259318547402919942363649L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=1000000000000000000L, 
                                code='`\x1aa\x01\x00\n`\x00U`\x1a`\xff\n`\x01U`\x1aa\x01\x01\n'\
                                     '`\x02U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069521887415590932569929099639409724315265L
        price = 100000000000000L
        data = ''
        caller = 1170859069521887415590932569929099639409724315265L
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

    def test_expPowerOf256_25(self):
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
                             'balance': 1000000000000000000L,
                             'code': '`\x19a\x01\x00\n`\x00U`\x19`\xff\n`\x01U`\x19a\x01\x01\n`\x02U',
                             'storage': {
                              0L: 1606938044258990275541962092341162602522202993782792835301376L,
                              1L: 1457150839514236217348081292704062901661172807216644287109375L,
                              2L: 1771446674072174508225286450717886232339530422363435486157057L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=1000000000000000000L, 
                                code='`\x19a\x01\x00\n`\x00U`\x19`\xff\n`\x01U`\x19a\x01\x01\n'\
                                     '`\x02U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069521887415590932569929099639409724315265L
        price = 100000000000000L
        data = ''
        caller = 1170859069521887415590932569929099639409724315265L
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

    def test_expPowerOf256_24(self):
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
                             'balance': 1000000000000000000L,
                             'code': '`\x18a\x01\x00\n`\x00U`\x18`\xff\n`\x01U`\x18a\x01\x01\n`\x02U',
                             'storage': {
                              0L: 6277101735386680763835789423207666416102355444464034512896L,
                              1L: 5714317017702887126855220755702207457494795322418212890625L,
                              2L: 6892788615066826880254032882170763549959262343826597222401L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=1000000000000000000L, 
                                code='`\x18a\x01\x00\n`\x00U`\x18`\xff\n`\x01U`\x18a\x01\x01\n'\
                                     '`\x02U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069521887415590932569929099639409724315265L
        price = 100000000000000L
        data = ''
        caller = 1170859069521887415590932569929099639409724315265L
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

    def test_addmodBigIntCast(self):
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
                             'balance': 1000000000000000000L,
                             'code': '`\x05`\x01\x7f\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\x08`\x00U',
                             'storage': {
                              0L: 1L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=1000000000000000000L, 
                                code='`\x05`\x01\x7f\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff'\
                                     '\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\x08`\x00U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069521887415590932569929099639409724315265L
        price = 100000000000000L
        data = ''
        caller = 1170859069521887415590932569929099639409724315265L
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

    def test_signextend_BigByteBigByte(self):
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
                             'balance': 1000000000000000000L,
                             'code': '\x7f\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\x7f\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\x0b`\x00U',
                             'storage': {
                              0L: 115792089237316195423570985008687907853269984665640564039457584007913129639935L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=1000000000000000000L, 
                                code='\x7f\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff'\
                                     '\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\x7f\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff'\
                                     '\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\x0b`\x00'\
                                     'U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069521887415590932569929099639409724315265L
        price = 100000000000000L
        data = ''
        caller = 1170859069521887415590932569929099639409724315265L
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

    def test_addmod1_overflow3(self):
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
                             'balance': 1000000000000000000L,
                             'code': '`\x05`\x01`\x01`\x00\x03\x08`\x00U',
                             'storage': {
                              0L: 1L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=1000000000000000000L, 
                                code='`\x05`\x01`\x01`\x00\x03\x08`\x00U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069521887415590932569929099639409724315265L
        price = 100000000000000L
        data = ''
        caller = 1170859069521887415590932569929099639409724315265L
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

    def test_mulUnderFlow(self):
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
                                balance=1000000000000000000L, 
                                code='`\x01\x02`\x01U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069521887415590932569929099639409724315265L
        price = 100000000000000L
        data = ''
        caller = 1170859069521887415590932569929099639409724315265L
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

    def test_expPowerOf256Of256_19(self):
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
                             'balance': 1000000000000000000L,
                             'code': '`\x13a\x01\x00\na\x01\x00\n`\x00U`\x13`\xff\na\x01\x00\n`\x01U`\x13a\x01\x01\na\x01\x00\n`\x02U`\x13a\x01\x00\n`\xff\n`\x03U`\x13`\xff\n`\xff\n`\x04U`\x13a\x01\x01\n`\xff\n`'\
                             '\x05U`\x13a\x01\x00\na\x01\x01\n`\x06U`\x13`\xff\na\x01\x01\n`\x07U`\x13a\x01\x01\na\x01\x01\n`\x08U',
                             'storage': {
                              3L: 58844010661592151918021960971670148005098640888438884074991120880745465249793L,
                              4L: 83037708815083470159439176343059806764476791572127774164450033570118131384063L,
                              5L: 14042401781101581299243232317313523558021645308348755647897149924594173542655L,
                              6L: 80031109568047806892179495136963220151591982015680194332645608881349571117057L,
                              7L: 78403999583194856336034090665674264222542182810896154607883723354325233434369L,
                              8L: 98020625165909217120717684081299357790464904257325036365510282840011357487361L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=1000000000000000000L, 
                                code='`\x13a\x01\x00\na\x01\x00\n`\x00U`\x13`\xff\na\x01\x00\n`'\
                                     '\x01U`\x13a\x01\x01\na\x01\x00\n`\x02U`\x13a\x01\x00\n`\xff'\
                                     '\n`\x03U`\x13`\xff\n`\xff\n`\x04U`\x13a\x01\x01\n`\xff'\
                                     '\n`\x05U`\x13a\x01\x00\na\x01\x01\n`\x06U`\x13`\xff\na'\
                                     '\x01\x01\n`\x07U`\x13a\x01\x01\na\x01\x01\n`\x08U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069521887415590932569929099639409724315265L
        price = 100000000000000L
        data = ''
        caller = 1170859069521887415590932569929099639409724315265L
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

    def test_expPowerOf256Of256_18(self):
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
                             'balance': 1000000000000000000L,
                             'code': '`\x12a\x01\x00\na\x01\x00\n`\x00U`\x12`\xff\na\x01\x00\n`\x01U`\x12a\x01\x01\na\x01\x00\n`\x02U`\x12a\x01\x00\n`\xff\n`\x03U`\x12`\xff\n`\xff\n`\x04U`\x12a\x01\x01\n`\xff\n`'\
                             '\x05U`\x12a\x01\x00\na\x01\x01\n`\x06U`\x12`\xff\na\x01\x01\n`\x07U`\x12a\x01\x01\na\x01\x01\n`\x08U',
                             'storage': {
                              3L: 47722708517889815122628810105015236221087683713987101985226708756686031552513L,
                              4L: 62498223098821962733903061319732317376595162521044937752089040386950014304511L,
                              5L: 87617296414069687466701422777716467712815533019690209856230187888840918827263L,
                              6L: 91227504086986730808710732351106377729136167577380599868217265603405814956033L,
                              7L: 29421361713313315972990398225990402447830660289868159244224680982816723173633L,
                              8L: 110931130223540473897795733757531375082108475243595043250924744061846069313793L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=1000000000000000000L, 
                                code='`\x12a\x01\x00\na\x01\x00\n`\x00U`\x12`\xff\na\x01\x00\n`'\
                                     '\x01U`\x12a\x01\x01\na\x01\x00\n`\x02U`\x12a\x01\x00\n`\xff'\
                                     '\n`\x03U`\x12`\xff\n`\xff\n`\x04U`\x12a\x01\x01\n`\xff'\
                                     '\n`\x05U`\x12a\x01\x00\na\x01\x01\n`\x06U`\x12`\xff\na'\
                                     '\x01\x01\n`\x07U`\x12a\x01\x01\na\x01\x01\n`\x08U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069521887415590932569929099639409724315265L
        price = 100000000000000L
        data = ''
        caller = 1170859069521887415590932569929099639409724315265L
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

    def test_expPowerOf2_8(self):
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
                             'balance': 1000000000000000000L,
                             'code': '`\x08`\x02\n`\x00U`\x07`\x02\n`\x01U`\t`\x02\n`\x02U',
                             'storage': {
                              0L: 256L,
                              1L: 128L,
                              2L: 512L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=1000000000000000000L, 
                                code='`\x08`\x02\n`\x00U`\x07`\x02\n`\x01U`\t`\x02\n`\x02'\
                                     'U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069521887415590932569929099639409724315265L
        price = 100000000000000L
        data = ''
        caller = 1170859069521887415590932569929099639409724315265L
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

    def test_expPowerOf256Of256_11(self):
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
                             'balance': 1000000000000000000L,
                             'code': '`\x0ba\x01\x00\na\x01\x00\n`\x00U`\x0b`\xff\na\x01\x00\n`\x01U`\x0ba\x01\x01\na\x01\x00\n`\x02U`\x0ba\x01\x00\n`\xff\n`\x03U`\x0b`\xff\n`\xff\n`\x04U`\x0ba\x01\x01\n`\xff\n`'\
                             '\x05U`\x0ba\x01\x00\na\x01\x01\n`\x06U`\x0b`\xff\na\x01\x01\n`\x07U`\x0ba\x01\x01\na\x01\x01\n`\x08U',
                             'storage': {
                              3L: 101890553050602617754926015251507180655045683544561831677215663393899651530753L,
                              4L: 18699204107595983543960872109239991216796489027696178041447150619885834993407L,
                              5L: 28030588289907797419557822587653826454800612063029355821581199851736896569599L,
                              6L: 46803055793531443315544302649156478669852813820237923809362846979832263213057L,
                              7L: 38012487980709084869740788615251142802769579500832552471564899673176158240513L,
                              8L: 99386799399269176133460845920098250474961692612186547558407604211935236260097L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=1000000000000000000L, 
                                code='`\x0ba\x01\x00\na\x01\x00\n`\x00U`\x0b`\xff\na\x01\x00\n`'\
                                     '\x01U`\x0ba\x01\x01\na\x01\x00\n`\x02U`\x0ba\x01\x00\n`\xff'\
                                     '\n`\x03U`\x0b`\xff\n`\xff\n`\x04U`\x0ba\x01\x01\n`\xff'\
                                     '\n`\x05U`\x0ba\x01\x00\na\x01\x01\n`\x06U`\x0b`\xff\na'\
                                     '\x01\x01\n`\x07U`\x0ba\x01\x01\na\x01\x01\n`\x08U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069521887415590932569929099639409724315265L
        price = 100000000000000L
        data = ''
        caller = 1170859069521887415590932569929099639409724315265L
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

    def test_expPowerOf256Of256_10(self):
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
                             'balance': 1000000000000000000L,
                             'code': '`\na\x01\x00\na\x01\x00\n`\x00U`\n`\xff\na\x01\x00\n`\x01U`\na\x01\x01\na\x01\x00\n`\x02U`\na\x01\x00\n`\xff\n`\x03U`\n`\xff\n`\xff\n`\x04U`\na\x01\x01\n`\xff\n`'\
                             '\x05U`\na\x01\x00\na\x01\x01\n`\x06U`\n`\xff\na\x01\x01\n`\x07U`\na\x01\x01\na\x01\x01\n`\x08U',
                             'storage': {
                              3L: 114914632844046583933260134950687189314890709482596989657240944241417975234561L,
                              4L: 87710304769150807214235028736827993866595394348364203769770205211527048724735L,
                              5L: 39290610890452765349502690951550527297496048075653585758833528807928504123647L,
                              6L: 20484820853245168917669616382018121754787019534209236968739196776128530350081L,
                              7L: 11024531560426914560193215886265230714814461857853456442906740807421673210113L,
                              8L: 75819177417320365411421114579935983460137159977655625167576545660532198867201L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=1000000000000000000L, 
                                code='`\na\x01\x00\na\x01\x00\n`\x00U`\n`\xff\na\x01\x00\n`'\
                                     '\x01U`\na\x01\x01\na\x01\x00\n`\x02U`\na\x01\x00\n`\xff'\
                                     '\n`\x03U`\n`\xff\n`\xff\n`\x04U`\na\x01\x01\n`\xff'\
                                     '\n`\x05U`\na\x01\x00\na\x01\x01\n`\x06U`\n`\xff\na'\
                                     '\x01\x01\n`\x07U`\na\x01\x01\na\x01\x01\n`\x08U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069521887415590932569929099639409724315265L
        price = 100000000000000L
        data = ''
        caller = 1170859069521887415590932569929099639409724315265L
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

    def test_expPowerOf256Of256_13(self):
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
                             'balance': 1000000000000000000L,
                             'code': '`\ra\x01\x00\na\x01\x00\n`\x00U`\r`\xff\na\x01\x00\n`\x01U`\ra\x01\x01\na\x01\x00\n`\x02U`\ra\x01\x00\n`\xff\n`\x03U`\r`\xff\n`\xff\n`\x04U`\ra\x01\x01\n`\xff\n`'\
                             '\x05U`\ra\x01\x00\na\x01\x01\n`\x06U`\r`\xff\na\x01\x01\n`\x07U`\ra\x01\x01\na\x01\x01\n`\x08U',
                             'storage': {
                              3L: 101385611762951987714492031095649658484764376091855612650967395547963616919553L,
                              4L: 63278556072604564884482487087793889312459895451266827394465757221242014531327L,
                              5L: 76503832981956381614151500340961475340424985318231630606058029623855335407871L,
                              6L: 29704886013344757714156143369444407261954548115394473056019137567405601980417L,
                              7L: 6180831967313900224885719403625820907184847095809151480761496615548164636417L,
                              8L: 11715094450588063760202497755635816063485576587916768949517781391496719433985L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=1000000000000000000L, 
                                code='`\ra\x01\x00\na\x01\x00\n`\x00U`\r`\xff\na\x01\x00\n`'\
                                     '\x01U`\ra\x01\x01\na\x01\x00\n`\x02U`\ra\x01\x00\n`\xff'\
                                     '\n`\x03U`\r`\xff\n`\xff\n`\x04U`\ra\x01\x01\n`\xff'\
                                     '\n`\x05U`\ra\x01\x00\na\x01\x01\n`\x06U`\r`\xff\na'\
                                     '\x01\x01\n`\x07U`\ra\x01\x01\na\x01\x01\n`\x08U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069521887415590932569929099639409724315265L
        price = 100000000000000L
        data = ''
        caller = 1170859069521887415590932569929099639409724315265L
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

    def test_expPowerOf256Of256_12(self):
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
                             'balance': 1000000000000000000L,
                             'code': '`\x0ca\x01\x00\na\x01\x00\n`\x00U`\x0c`\xff\na\x01\x00\n`\x01U`\x0ca\x01\x01\na\x01\x00\n`\x02U`\x0ca\x01\x00\n`\xff\n`\x03U`\x0c`\xff\n`\xff\n`\x04U`\x0ca\x01\x01\n`\xff\n`'\
                             '\x05U`\x0ca\x01\x00\na\x01\x01\n`\x06U`\x0c`\xff\na\x01\x01\n`\x07U`\x0ca\x01\x01\na\x01\x01\n`\x08U',
                             'storage': {
                              3L: 80019368324629526638747930237288975316558411254569129739228874063734837870593L,
                              4L: 88884190982786141138179309319347702000408571864083758904533741801152047218943L,
                              5L: 93752052283216392393116198718556172755601810993178115549913696304169392799999L,
                              6L: 74991547227499153688926126987451352010669639751209250187538225368170577788929L,
                              7L: 27079447990334421832768535213001382538364337104003887072154060444218791559425L,
                              8L: 28625806625801789859034042498407601320406435797081589212686750536894719459585L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=1000000000000000000L, 
                                code='`\x0ca\x01\x00\na\x01\x00\n`\x00U`\x0c`\xff\na\x01\x00\n`'\
                                     '\x01U`\x0ca\x01\x01\na\x01\x00\n`\x02U`\x0ca\x01\x00\n`\xff'\
                                     '\n`\x03U`\x0c`\xff\n`\xff\n`\x04U`\x0ca\x01\x01\n`\xff'\
                                     '\n`\x05U`\x0ca\x01\x00\na\x01\x01\n`\x06U`\x0c`\xff\na'\
                                     '\x01\x01\n`\x07U`\x0ca\x01\x01\na\x01\x01\n`\x08U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069521887415590932569929099639409724315265L
        price = 100000000000000L
        data = ''
        caller = 1170859069521887415590932569929099639409724315265L
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

    def test_expPowerOf256Of256_15(self):
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
                             'balance': 1000000000000000000L,
                             'code': '`\x0fa\x01\x00\na\x01\x00\n`\x00U`\x0f`\xff\na\x01\x00\n`\x01U`\x0fa\x01\x01\na\x01\x00\n`\x02U`\x0fa\x01\x00\n`\xff\n`\x03U`\x0f`\xff\n`\xff\n`\x04U`\x0fa\x01\x01\n`\xff\n`'\
                             '\x05U`\x0fa\x01\x00\na\x01\x01\n`\x06U`\x0f`\xff\na\x01\x01\n`\x07U`\x0fa\x01\x01\na\x01\x01\n`\x08U',
                             'storage': {
                              3L: 68982874759710612496975781615902521595583884631451676122827056878494762926081L,
                              4L: 53267908598997767238534137623343245537541072806296987245216780723497328312063L,
                              5L: 41822178356738160566095801792837818951900117455658262420410104537286555140351L,
                              6L: 86452819266916911147472883657170177834027340189490420841254375251628114575361L,
                              7L: 89845175342602369207035384471933876015521364174370333412283388556428862029569L,
                              8L: 104349806891036036967003847033901513956038759123355017779183952015787964694785L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=1000000000000000000L, 
                                code='`\x0fa\x01\x00\na\x01\x00\n`\x00U`\x0f`\xff\na\x01\x00\n`'\
                                     '\x01U`\x0fa\x01\x01\na\x01\x00\n`\x02U`\x0fa\x01\x00\n`\xff'\
                                     '\n`\x03U`\x0f`\xff\n`\xff\n`\x04U`\x0fa\x01\x01\n`\xff'\
                                     '\n`\x05U`\x0fa\x01\x00\na\x01\x01\n`\x06U`\x0f`\xff\na'\
                                     '\x01\x01\n`\x07U`\x0fa\x01\x01\na\x01\x01\n`\x08U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069521887415590932569929099639409724315265L
        price = 100000000000000L
        data = ''
        caller = 1170859069521887415590932569929099639409724315265L
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

    def test_expPowerOf256Of256_14(self):
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
                             'balance': 1000000000000000000L,
                             'code': '`\x0ea\x01\x00\na\x01\x00\n`\x00U`\x0e`\xff\na\x01\x00\n`\x01U`\x0ea\x01\x01\na\x01\x00\n`\x02U`\x0ea\x01\x00\n`\xff\n`\x03U`\x0e`\xff\n`\xff\n`\x04U`\x0ea\x01\x01\n`\xff\n`'\
                             '\x05U`\x0ea\x01\x00\na\x01\x01\n`\x06U`\x0e`\xff\na\x01\x01\n`\x07U`\x0ea\x01\x01\na\x01\x01\n`\x08U',
                             'storage': {
                              3L: 99326861617797847825989094377338474355592720485724747187463584063301701599233L,
                              4L: 59695912561066707238569545894561715648962424372877657499564472558682379518207L,
                              5L: 28709703754750430860229520230767157586576999441276879698135528982523256111359L,
                              6L: 101656667831445454371959219483138111838033319621999128300415596713351307067393L,
                              7L: 58439732298837688121708859932549010044236910193436024683432213454604389712129L,
                              8L: 92859850393288921948278045707683108445628062778327872864204574351935748833537L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=1000000000000000000L, 
                                code='`\x0ea\x01\x00\na\x01\x00\n`\x00U`\x0e`\xff\na\x01\x00\n`'\
                                     '\x01U`\x0ea\x01\x01\na\x01\x00\n`\x02U`\x0ea\x01\x00\n`\xff'\
                                     '\n`\x03U`\x0e`\xff\n`\xff\n`\x04U`\x0ea\x01\x01\n`\xff'\
                                     '\n`\x05U`\x0ea\x01\x00\na\x01\x01\n`\x06U`\x0e`\xff\na'\
                                     '\x01\x01\n`\x07U`\x0ea\x01\x01\na\x01\x01\n`\x08U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069521887415590932569929099639409724315265L
        price = 100000000000000L
        data = ''
        caller = 1170859069521887415590932569929099639409724315265L
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

    def test_expPowerOf256Of256_17(self):
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
                             'balance': 1000000000000000000L,
                             'code': '`\x11a\x01\x00\na\x01\x00\n`\x00U`\x11`\xff\na\x01\x00\n`\x01U`\x11a\x01\x01\na\x01\x00\n`\x02U`\x11a\x01\x00\n`\xff\n`\x03U`\x11`\xff\n`\xff\n`\x04U`\x11a\x01\x01\n`\xff\n`'\
                             '\x05U`\x11a\x01\x00\na\x01\x01\n`\x06U`\x11`\xff\na\x01\x01\n`\x07U`\x11a\x01\x01\na\x01\x01\n`\x08U',
                             'storage': {
                              3L: 106932249095798874746427270594356880818721890878145157091004752088375721197569L,
                              4L: 51639322353743519847823032836772280028397740691078922235532368225465122422527L,
                              5L: 62775564944078456192298461614676049908347327243429853520972071233715122012415L,
                              6L: 65037094785246885454606881205443270315416968651421801787150983510683528724481L,
                              7L: 58726458517348185850456409500813811723249871888157665424521042251051315625729L,
                              8L: 70752790625743581923020113660624109695844588519198843885497132740742925582593L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=1000000000000000000L, 
                                code='`\x11a\x01\x00\na\x01\x00\n`\x00U`\x11`\xff\na\x01\x00\n`'\
                                     '\x01U`\x11a\x01\x01\na\x01\x00\n`\x02U`\x11a\x01\x00\n`\xff'\
                                     '\n`\x03U`\x11`\xff\n`\xff\n`\x04U`\x11a\x01\x01\n`\xff'\
                                     '\n`\x05U`\x11a\x01\x00\na\x01\x01\n`\x06U`\x11`\xff\na'\
                                     '\x01\x01\n`\x07U`\x11a\x01\x01\na\x01\x01\n`\x08U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069521887415590932569929099639409724315265L
        price = 100000000000000L
        data = ''
        caller = 1170859069521887415590932569929099639409724315265L
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

    def test_expPowerOf256Of256_16(self):
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
                             'balance': 1000000000000000000L,
                             'code': '`\x10a\x01\x00\na\x01\x00\n`\x00U`\x10`\xff\na\x01\x00\n`\x01U`\x10a\x01\x01\na\x01\x00\n`\x02U`\x10a\x01\x00\n`\xff\n`\x03U`\x10`\xff\n`\xff\n`\x04U`\x10a\x01\x01\n`\xff\n`'\
                             '\x05U`\x10a\x01\x00\na\x01\x01\n`\x06U`\x10`\xff\na\x01\x01\n`\x07U`\x10a\x01\x01\na\x01\x01\n`\x08U',
                             'storage': {
                              3L: 59218374413855094843010372350483534772436796474263353446173791691863603806209L,
                              4L: 22225091498890937679096212997872924330088689197184547205512400761506168307967L,
                              5L: 48021548981484736825763261181421514354558065935321217017669311494625227178239L,
                              6L: 15632688003335927851000079576175125536432017372200003824721518905389570064385L,
                              7L: 61912347378855182565924718380527615965311347792179366367697517640802114732289L,
                              8L: 33499807378575975745280476771049124131850159969595906991504434239871965462785L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=1000000000000000000L, 
                                code='`\x10a\x01\x00\na\x01\x00\n`\x00U`\x10`\xff\na\x01\x00\n`'\
                                     '\x01U`\x10a\x01\x01\na\x01\x00\n`\x02U`\x10a\x01\x00\n`\xff'\
                                     '\n`\x03U`\x10`\xff\n`\xff\n`\x04U`\x10a\x01\x01\n`\xff'\
                                     '\n`\x05U`\x10a\x01\x00\na\x01\x01\n`\x06U`\x10`\xff\na'\
                                     '\x01\x01\n`\x07U`\x10a\x01\x01\na\x01\x01\n`\x08U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069521887415590932569929099639409724315265L
        price = 100000000000000L
        data = ''
        caller = 1170859069521887415590932569929099639409724315265L
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

    def test_addmod1_overflow2(self):
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
                             'balance': 1000000000000000000L,
                             'code': '`\x05`\x00`\x01`\x00\x03\x08`\x00U',
                             'storage': {
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=1000000000000000000L, 
                                code='`\x05`\x00`\x01`\x00\x03\x08`\x00U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069521887415590932569929099639409724315265L
        price = 100000000000000L
        data = ''
        caller = 1170859069521887415590932569929099639409724315265L
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

    def test_expXY_success(self):
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
                             'balance': 1000000000000000000L,
                             'code': '`\x005`\x00U` 5`\x01U`\x01T`\x00T\n`\x02U',
                             'storage': {
                              0L: 2L,
                              1L: 15L,
                              2L: 32768L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=1000000000000000000L, 
                                code='`\x005`\x00U` 5`\x01U`\x01T`\x00T\n`\x02U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069521887415590932569929099639409724315265L
        price = 100000000000000L
        data = '\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x02\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x0f'
        caller = 1170859069521887415590932569929099639409724315265L
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

    def test_expPowerOf256Of256_26(self):
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
                             'balance': 1000000000000000000L,
                             'code': '`\x1aa\x01\x00\na\x01\x00\n`\x00U`\x1a`\xff\na\x01\x00\n`\x01U`\x1aa\x01\x01\na\x01\x00\n`\x02U`\x1aa\x01\x00\n`\xff\n`\x03U`\x1a`\xff\n`\xff\n`\x04U`\x1aa\x01\x01\n`\xff\n`'\
                             '\x05U`\x1aa\x01\x00\na\x01\x01\n`\x06U`\x1a`\xff\na\x01\x01\n`\x07U`\x1aa\x01\x01\na\x01\x01\n`\x08U',
                             'storage': {
                              3L: 3768829712260290751596832614926327440601038856186643509120209088559741665281L,
                              4L: 13156479618473122453827333675314833413833735874110900611322468555500321898751L,
                              5L: 63130786578447000143359706132655438781703096764577257433234668088023930503423L,
                              6L: 112022376074563568812658720950344193866391401393868338298317741635149131415553L,
                              7L: 47580733608497810153764935870993478768529823747464839196957117315105893515521L,
                              8L: 23524974130592294778780884663680818889754585050430865625920211481456128164097L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=1000000000000000000L, 
                                code='`\x1aa\x01\x00\na\x01\x00\n`\x00U`\x1a`\xff\na\x01\x00\n`'\
                                     '\x01U`\x1aa\x01\x01\na\x01\x00\n`\x02U`\x1aa\x01\x00\n`\xff'\
                                     '\n`\x03U`\x1a`\xff\n`\xff\n`\x04U`\x1aa\x01\x01\n`\xff'\
                                     '\n`\x05U`\x1aa\x01\x00\na\x01\x01\n`\x06U`\x1a`\xff\na'\
                                     '\x01\x01\n`\x07U`\x1aa\x01\x01\na\x01\x01\n`\x08U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069521887415590932569929099639409724315265L
        price = 100000000000000L
        data = ''
        caller = 1170859069521887415590932569929099639409724315265L
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

    def test_expPowerOf256_18(self):
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
                             'balance': 1000000000000000000L,
                             'code': '`\x12a\x01\x00\n`\x00U`\x12`\xff\n`\x01U`\x12a\x01\x01\n`\x02U',
                             'storage': {
                              0L: 22300745198530623141535718272648361505980416L,
                              1L: 20783718319962978657280835660556793212890625L,
                              2L: 23921930261174538048551511546295524724904449L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=1000000000000000000L, 
                                code='`\x12a\x01\x00\n`\x00U`\x12`\xff\n`\x01U`\x12a\x01\x01\n'\
                                     '`\x02U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069521887415590932569929099639409724315265L
        price = 100000000000000L
        data = ''
        caller = 1170859069521887415590932569929099639409724315265L
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

    def test_expPowerOf256_19(self):
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
                             'balance': 1000000000000000000L,
                             'code': '`\x13a\x01\x00\n`\x00U`\x13`\xff\n`\x01U`\x13a\x01\x01\n`\x02U',
                             'storage': {
                              0L: 5708990770823839524233143877797980545530986496L,
                              1L: 5299848171590559557606613093441982269287109375L,
                              2L: 6147936077121856278477738467397949854300443393L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=1000000000000000000L, 
                                code='`\x13a\x01\x00\n`\x00U`\x13`\xff\n`\x01U`\x13a\x01\x01\n'\
                                     '`\x02U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069521887415590932569929099639409724315265L
        price = 100000000000000L
        data = ''
        caller = 1170859069521887415590932569929099639409724315265L
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

    def test_expPowerOf256_16(self):
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
                             'balance': 1000000000000000000L,
                             'code': '`\x10a\x01\x00\n`\x00U`\x10`\xff\n`\x01U`\x10a\x01\x01\n`\x02U',
                             'storage': {
                              0L: 340282366920938463463374607431768211456L,
                              1L: 319626579315078487616775634918212890625L,
                              2L: 362184594182720980613658216570962841601L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=1000000000000000000L, 
                                code='`\x10a\x01\x00\n`\x00U`\x10`\xff\n`\x01U`\x10a\x01\x01\n'\
                                     '`\x02U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069521887415590932569929099639409724315265L
        price = 100000000000000L
        data = ''
        caller = 1170859069521887415590932569929099639409724315265L
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

    def test_expPowerOf256_17(self):
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
                             'balance': 1000000000000000000L,
                             'code': '`\x11a\x01\x00\n`\x00U`\x11`\xff\n`\x01U`\x11a\x01\x01\n`\x02U',
                             'storage': {
                              0L: 87112285931760246646623899502532662132736L,
                              1L: 81504777725345014342277786904144287109375L,
                              2L: 93081440704959292017710161658737450291457L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=1000000000000000000L, 
                                code='`\x11a\x01\x00\n`\x00U`\x11`\xff\n`\x01U`\x11a\x01\x01\n'\
                                     '`\x02U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069521887415590932569929099639409724315265L
        price = 100000000000000L
        data = ''
        caller = 1170859069521887415590932569929099639409724315265L
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

    def test_expPowerOf256_14(self):
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
                             'balance': 1000000000000000000L,
                             'code': '`\x0ea\x01\x00\n`\x00U`\x0e`\xff\n`\x01U`\x0ea\x01\x01\n`\x02U',
                             'storage': {
                              0L: 5192296858534827628530496329220096L,
                              1L: 4915441435064644177113043212890625L,
                              2L: 5483574227962890893331590433934849L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=1000000000000000000L, 
                                code='`\x0ea\x01\x00\n`\x00U`\x0e`\xff\n`\x01U`\x0ea\x01\x01\n'\
                                     '`\x02U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069521887415590932569929099639409724315265L
        price = 100000000000000L
        data = ''
        caller = 1170859069521887415590932569929099639409724315265L
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

    def test_expPowerOf256_15(self):
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
                             'balance': 1000000000000000000L,
                             'code': '`\x0fa\x01\x00\n`\x00U`\x0f`\xff\n`\x01U`\x0fa\x01\x01\n`\x02U',
                             'storage': {
                              0L: 1329227995784915872903807060280344576L,
                              1L: 1253437565941484265163826019287109375L,
                              2L: 1409278576586462959586218741521256193L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=1000000000000000000L, 
                                code='`\x0fa\x01\x00\n`\x00U`\x0f`\xff\n`\x01U`\x0fa\x01\x01\n'\
                                     '`\x02U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069521887415590932569929099639409724315265L
        price = 100000000000000L
        data = ''
        caller = 1170859069521887415590932569929099639409724315265L
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

    def test_expPowerOf256_12(self):
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
                             'balance': 1000000000000000000L,
                             'code': '`\x0ca\x01\x00\n`\x00U`\x0c`\xff\n`\x01U`\x0ca\x01\x01\n`\x02U',
                             'storage': {
                              0L: 79228162514264337593543950336L,
                              1L: 75593101654204447168212890625L,
                              2L: 83022819845310162051379891201L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=1000000000000000000L, 
                                code='`\x0ca\x01\x00\n`\x00U`\x0c`\xff\n`\x01U`\x0ca\x01\x01\n'\
                                     '`\x02U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069521887415590932569929099639409724315265L
        price = 100000000000000L
        data = ''
        caller = 1170859069521887415590932569929099639409724315265L
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

    def test_expPowerOf256_13(self):
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
                             'balance': 1000000000000000000L,
                             'code': '`\ra\x01\x00\n`\x00U`\r`\xff\n`\x01U`\ra\x01\x01\n`\x02U',
                             'storage': {
                              0L: 20282409603651670423947251286016L,
                              1L: 19276240921822134027894287109375L,
                              2L: 21336864700244711647204632038657L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=1000000000000000000L, 
                                code='`\ra\x01\x00\n`\x00U`\r`\xff\n`\x01U`\ra\x01\x01\n'\
                                     '`\x02U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069521887415590932569929099639409724315265L
        price = 100000000000000L
        data = ''
        caller = 1170859069521887415590932569929099639409724315265L
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

    def test_expPowerOf256_10(self):
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
                             'balance': 1000000000000000000L,
                             'code': '`\na\x01\x00\n`\x00U`\n`\xff\n`\x01U`\na\x01\x01\n`\x02U',
                             'storage': {
                              0L: 1208925819614629174706176L,
                              1L: 1162523670191533212890625L,
                              2L: 1256988294225653106805249L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=1000000000000000000L, 
                                code='`\na\x01\x00\n`\x00U`\n`\xff\n`\x01U`\na\x01\x01\n'\
                                     '`\x02U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069521887415590932569929099639409724315265L
        price = 100000000000000L
        data = ''
        caller = 1170859069521887415590932569929099639409724315265L
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

    def test_expPowerOf256_11(self):
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
                             'balance': 1000000000000000000L,
                             'code': '`\x0ba\x01\x00\n`\x00U`\x0b`\xff\n`\x01U`\x0ba\x01\x01\n`\x02U',
                             'storage': {
                              0L: 309485009821345068724781056L,
                              1L: 296443535898840969287109375L,
                              2L: 323045991615992848448948993L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=1000000000000000000L, 
                                code='`\x0ba\x01\x00\n`\x00U`\x0b`\xff\n`\x01U`\x0ba\x01\x01\n'\
                                     '`\x02U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069521887415590932569929099639409724315265L
        price = 100000000000000L
        data = ''
        caller = 1170859069521887415590932569929099639409724315265L
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

    def test_mulmoddivByZero2(self):
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
                             'balance': 1000000000000000000L,
                             'code': '`\x00`\x00`\x01\t`\x00U',
                             'storage': {
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=1000000000000000000L, 
                                code='`\x00`\x00`\x01\t`\x00U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069521887415590932569929099639409724315265L
        price = 100000000000000L
        data = ''
        caller = 1170859069521887415590932569929099639409724315265L
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

    def test_mulmoddivByZero3(self):
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
                             'balance': 1000000000000000000L,
                             'code': '`\x00`\x00`\x00\t`\x01\x03`\x00U',
                             'storage': {
                              0L: 1L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=1000000000000000000L, 
                                code='`\x00`\x00`\x00\t`\x01\x03`\x00U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069521887415590932569929099639409724315265L
        price = 100000000000000L
        data = ''
        caller = 1170859069521887415590932569929099639409724315265L
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

    def test_mulmoddivByZero1(self):
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
                             'balance': 1000000000000000000L,
                             'code': '`\x00`\x01`\x00\t`\x00U',
                             'storage': {
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=1000000000000000000L, 
                                code='`\x00`\x01`\x00\t`\x00U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069521887415590932569929099639409724315265L
        price = 100000000000000L
        data = ''
        caller = 1170859069521887415590932569929099639409724315265L
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

    def test_sdiv_i256min2(self):
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
                             'balance': 1000000000000000000L,
                             'code': '`\x01`\x00\x03\x7f\x80\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00`\x00\x03\x05`\x00U',
                             'storage': {
                              0L: 57896044618658097711785492504343953926634992332820282019728792003956564819968L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=1000000000000000000L, 
                                code='`\x01`\x00\x03\x7f\x80\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00'\
                                     '\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00`\x00\x03\x05`\x00U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069521887415590932569929099639409724315265L
        price = 100000000000000L
        data = ''
        caller = 1170859069521887415590932569929099639409724315265L
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

    def test_sdiv_i256min3(self):
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
                             'balance': 1000000000000000000L,
                             'code': '\x7f\x7f\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff`\x00\x03\x7f\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\x05`'\
                             '\x00U',
                             'storage': {
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=1000000000000000000L, 
                                code='\x7f\x7f\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff'\
                                     '\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff`\x00\x03\x7f\xff\xff\xff\xff\xff\xff\xff\xff\xff'\
                                     '\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff'\
                                     '\x05`\x00U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069521887415590932569929099639409724315265L
        price = 1L
        data = ''
        caller = 1170859069521887415590932569929099639409724315265L
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

    def test_fibbonacci_unrolled(self):
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
                             'balance': 1000000000000000000L,
                             'code': '`\x01`\x01\x81\x81\x01\x81\x81\x01\x81\x81\x01\x81\x81\x01\x81\x81\x01\x81\x81\x01\x81\x81\x01\x81\x81\x01\x81\x81\x01\x81\x81\x01\x81\x81\x01\x81\x81\x01\x81\x81\x01\x81\x81\x01\x81\x81\x01\x81\x81\x01\x81\x81\x01`\x00R` `\x00\xf3',
                             'storage': {
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=1000000000000000000L, 
                                code='`\x01`\x01\x81\x81\x01\x81\x81\x01\x81\x81\x01\x81\x81\x01\x81\x81\x01\x81\x81\x01\x81'\
                                     '\x81\x01\x81\x81\x01\x81\x81\x01\x81\x81\x01\x81\x81\x01\x81\x81\x01\x81\x81\x01\x81\x81\x01'\
                                     '\x81\x81\x01\x81\x81\x01\x81\x81\x01`\x00R` `\x00\xf3', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069521887415590932569929099639409724315265L
        price = 100000000000000L
        data = ''
        caller = 1170859069521887415590932569929099639409724315265L
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

    def test_divByZero(self):
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
                             'balance': 1000000000000000000L,
                             'code': '`\x00`\x02\x04`\x00U',
                             'storage': {
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=1000000000000000000L, 
                                code='`\x00`\x02\x04`\x00U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069521887415590932569929099639409724315265L
        price = 100000000000000L
        data = ''
        caller = 1170859069521887415590932569929099639409724315265L
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

    def test_signextend_00(self):
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
                             'balance': 1000000000000000000L,
                             'code': '`\x00`\x00\x0b`\x00U',
                             'storage': {
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=1000000000000000000L, 
                                code='`\x00`\x00\x0b`\x00U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069521887415590932569929099639409724315265L
        price = 100000000000000L
        data = ''
        caller = 1170859069521887415590932569929099639409724315265L
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

    def test_expPowerOf256_4(self):
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
                             'balance': 1000000000000000000L,
                             'code': '`\x04a\x01\x00\n`\x00U`\x04`\xff\n`\x01U`\x04a\x01\x01\n`\x02U',
                             'storage': {
                              0L: 4294967296L,
                              1L: 4228250625L,
                              2L: 4362470401L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=1000000000000000000L, 
                                code='`\x04a\x01\x00\n`\x00U`\x04`\xff\n`\x01U`\x04a\x01\x01\n'\
                                     '`\x02U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069521887415590932569929099639409724315265L
        price = 100000000000000L
        data = ''
        caller = 1170859069521887415590932569929099639409724315265L
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

    def test_expPowerOf256_5(self):
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
                             'balance': 1000000000000000000L,
                             'code': '`\x05a\x01\x00\n`\x00U`\x05`\xff\n`\x01U`\x05a\x01\x01\n`\x02U',
                             'storage': {
                              0L: 1099511627776L,
                              1L: 1078203909375L,
                              2L: 1121154893057L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=1000000000000000000L, 
                                code='`\x05a\x01\x00\n`\x00U`\x05`\xff\n`\x01U`\x05a\x01\x01\n'\
                                     '`\x02U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069521887415590932569929099639409724315265L
        price = 100000000000000L
        data = ''
        caller = 1170859069521887415590932569929099639409724315265L
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

    def test_expPowerOf256_6(self):
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
                             'balance': 1000000000000000000L,
                             'code': '`\x06a\x01\x00\n`\x00U`\x06`\xff\n`\x01U`\x06a\x01\x01\n`\x02U',
                             'storage': {
                              0L: 281474976710656L,
                              1L: 274941996890625L,
                              2L: 288136807515649L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=1000000000000000000L, 
                                code='`\x06a\x01\x00\n`\x00U`\x06`\xff\n`\x01U`\x06a\x01\x01\n'\
                                     '`\x02U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069521887415590932569929099639409724315265L
        price = 100000000000000L
        data = ''
        caller = 1170859069521887415590932569929099639409724315265L
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

    def test_expPowerOf256_7(self):
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
                             'balance': 1000000000000000000L,
                             'code': '`\x07a\x01\x00\n`\x00U`\x07`\xff\n`\x01U`\x07a\x01\x01\n`\x02U',
                             'storage': {
                              0L: 72057594037927936L,
                              1L: 70110209207109375L,
                              2L: 74051159531521793L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=1000000000000000000L, 
                                code='`\x07a\x01\x00\n`\x00U`\x07`\xff\n`\x01U`\x07a\x01\x01\n'\
                                     '`\x02U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069521887415590932569929099639409724315265L
        price = 100000000000000L
        data = ''
        caller = 1170859069521887415590932569929099639409724315265L
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

    def test_expPowerOf256_1(self):
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
                             'balance': 1000000000000000000L,
                             'code': '`\x01a\x01\x00\n`\x00U`\x01`\xff\n`\x01U`\x01a\x01\x01\n`\x02U',
                             'storage': {
                              0L: 256L,
                              1L: 255L,
                              2L: 257L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=1000000000000000000L, 
                                code='`\x01a\x01\x00\n`\x00U`\x01`\xff\n`\x01U`\x01a\x01\x01\n'\
                                     '`\x02U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069521887415590932569929099639409724315265L
        price = 100000000000000L
        data = ''
        caller = 1170859069521887415590932569929099639409724315265L
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

    def test_expPowerOf256_2(self):
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
                             'balance': 1000000000000000000L,
                             'code': '`\x02a\x01\x00\n`\x00U`\x02`\xff\n`\x01U`\x02a\x01\x01\n`\x02U',
                             'storage': {
                              0L: 65536L,
                              1L: 65025L,
                              2L: 66049L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=1000000000000000000L, 
                                code='`\x02a\x01\x00\n`\x00U`\x02`\xff\n`\x01U`\x02a\x01\x01\n'\
                                     '`\x02U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069521887415590932569929099639409724315265L
        price = 100000000000000L
        data = ''
        caller = 1170859069521887415590932569929099639409724315265L
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

    def test_expPowerOf256_3(self):
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
                             'balance': 1000000000000000000L,
                             'code': '`\x03a\x01\x00\n`\x00U`\x03`\xff\n`\x01U`\x03a\x01\x01\n`\x02U',
                             'storage': {
                              0L: 16777216L,
                              1L: 16581375L,
                              2L: 16974593L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=1000000000000000000L, 
                                code='`\x03a\x01\x00\n`\x00U`\x03`\xff\n`\x01U`\x03a\x01\x01\n'\
                                     '`\x02U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069521887415590932569929099639409724315265L
        price = 100000000000000L
        data = ''
        caller = 1170859069521887415590932569929099639409724315265L
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

    def test_mul2(self):
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
                             'balance': 1000000000000000000L,
                             'code': '`\x17`\x00\x02`\x00U',
                             'storage': {
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=1000000000000000000L, 
                                code='`\x17`\x00\x02`\x00U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069521887415590932569929099639409724315265L
        price = 100000000000000L
        data = ''
        caller = 1170859069521887415590932569929099639409724315265L
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

    def test_mul3(self):
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
                             'balance': 1000000000000000000L,
                             'code': '`\x01`\x17\x02`\x00U',
                             'storage': {
                              0L: 23L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=1000000000000000000L, 
                                code='`\x01`\x17\x02`\x00U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069521887415590932569929099639409724315265L
        price = 100000000000000L
        data = ''
        caller = 1170859069521887415590932569929099639409724315265L
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

    def test_mul0(self):
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
                             'balance': 1000000000000000000L,
                             'code': '`\x03`\x02\x02`\x00U',
                             'storage': {
                              0L: 6L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=1000000000000000000L, 
                                code='`\x03`\x02\x02`\x00U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069521887415590932569929099639409724315265L
        price = 100000000000000L
        data = ''
        caller = 1170859069521887415590932569929099639409724315265L
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

    def test_mul1(self):
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
                             'balance': 1000000000000000000L,
                             'code': '\x7f\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\x7f\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\x02`\x00U',
                             'storage': {
                              0L: 1L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=1000000000000000000L, 
                                code='\x7f\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff'\
                                     '\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\x7f\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff'\
                                     '\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\x02`\x00'\
                                     'U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069521887415590932569929099639409724315265L
        price = 100000000000000L
        data = ''
        caller = 1170859069521887415590932569929099639409724315265L
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

    def test_expPowerOf256_8(self):
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
                             'balance': 1000000000000000000L,
                             'code': '`\x08a\x01\x00\n`\x00U`\x08`\xff\n`\x01U`\x08a\x01\x01\n`\x02U',
                             'storage': {
                              0L: 18446744073709551616L,
                              1L: 17878103347812890625L,
                              2L: 19031147999601100801L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=1000000000000000000L, 
                                code='`\x08a\x01\x00\n`\x00U`\x08`\xff\n`\x01U`\x08a\x01\x01\n'\
                                     '`\x02U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069521887415590932569929099639409724315265L
        price = 100000000000000L
        data = ''
        caller = 1170859069521887415590932569929099639409724315265L
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

    def test_expPowerOf256_9(self):
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
                             'balance': 1000000000000000000L,
                             'code': '`\ta\x01\x00\n`\x00U`\t`\xff\n`\x01U`\ta\x01\x01\n`\x02U',
                             'storage': {
                              0L: 4722366482869645213696L,
                              1L: 4558916353692287109375L,
                              2L: 4891005035897482905857L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=1000000000000000000L, 
                                code='`\ta\x01\x00\n`\x00U`\t`\xff\n`\x01U`\ta\x01\x01\n'\
                                     '`\x02U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069521887415590932569929099639409724315265L
        price = 100000000000000L
        data = ''
        caller = 1170859069521887415590932569929099639409724315265L
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

    def test_mul4(self):
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
                             'balance': 1000000000000000000L,
                             'code': '\x7f\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\x7f\x80\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x02`\x00U',
                             'storage': {
                              0L: 57896044618658097711785492504343953926634992332820282019728792003956564819968L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=1000000000000000000L, 
                                code='\x7f\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff'\
                                     '\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\x7f\x80\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00'\
                                     '\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x02`\x00'\
                                     'U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069521887415590932569929099639409724315265L
        price = 100000000000000L
        data = ''
        caller = 1170859069521887415590932569929099639409724315265L
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

    def test_mul5(self):
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
                             'balance': 1000000000000000000L,
                             'code': '\x7f\x80\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x7f\x80\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x02`\x00U',
                             'storage': {
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=1000000000000000000L, 
                                code='\x7f\x80\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00'\
                                     '\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x7f\x80\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00'\
                                     '\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x02`\x00'\
                                     'U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069521887415590932569929099639409724315265L
        price = 100000000000000L
        data = ''
        caller = 1170859069521887415590932569929099639409724315265L
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

    def test_expPowerOf256Of256_7(self):
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
                             'balance': 1000000000000000000L,
                             'code': '`\x07a\x01\x00\na\x01\x00\n`\x00U`\x07`\xff\na\x01\x00\n`\x01U`\x07a\x01\x01\na\x01\x00\n`\x02U`\x07a\x01\x00\n`\xff\n`\x03U`\x07`\xff\n`\xff\n`\x04U`\x07a\x01\x01\n`\xff\n`'\
                             '\x05U`\x07a\x01\x00\na\x01\x01\n`\x06U`\x07`\xff\na\x01\x01\n`\x07U`\x07a\x01\x01\na\x01\x01\n`\x08U',
                             'storage': {
                              3L: 63182715569273074787714100940498879016211333097847191821758787388556590448641L,
                              4L: 76425605249543128808067971548918170160729791707747064947261918738976669564671L,
                              5L: 43345747554253238299465711077671703817838237369468988784434413112512838303999L,
                              6L: 90636177557414518135233707311441832681323290295963628475535580382064678010881L,
                              7L: 18310447951348423009296867942901618951251473555818375822006835637692098150145L,
                              8L: 4330632354923598824005817957634950183537333187179286018273483015945990897921L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=1000000000000000000L, 
                                code='`\x07a\x01\x00\na\x01\x00\n`\x00U`\x07`\xff\na\x01\x00\n`'\
                                     '\x01U`\x07a\x01\x01\na\x01\x00\n`\x02U`\x07a\x01\x00\n`\xff'\
                                     '\n`\x03U`\x07`\xff\n`\xff\n`\x04U`\x07a\x01\x01\n`\xff'\
                                     '\n`\x05U`\x07a\x01\x00\na\x01\x01\n`\x06U`\x07`\xff\na'\
                                     '\x01\x01\n`\x07U`\x07a\x01\x01\na\x01\x01\n`\x08U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069521887415590932569929099639409724315265L
        price = 100000000000000L
        data = ''
        caller = 1170859069521887415590932569929099639409724315265L
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

    def test_signextend_0_BigByte(self):
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
                             'balance': 1000000000000000000L,
                             'code': '\x7f\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff`\x00\x0b`\x00U',
                             'storage': {
                              0L: 115792089237316195423570985008687907853269984665640564039457584007913129639935L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=1000000000000000000L, 
                                code='\x7f\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff'\
                                     '\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff`\x00\x0b`\x00U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069521887415590932569929099639409724315265L
        price = 100000000000000L
        data = ''
        caller = 1170859069521887415590932569929099639409724315265L
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

    def test_addmodDivByZero(self):
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
                             'balance': 1000000000000000000L,
                             'code': '`\x00`\x01`\x04\x08`\x00U',
                             'storage': {
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=1000000000000000000L, 
                                code='`\x00`\x01`\x04\x08`\x00U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069521887415590932569929099639409724315265L
        price = 100000000000000L
        data = ''
        caller = 1170859069521887415590932569929099639409724315265L
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

    def test_expPowerOf256Of256_8(self):
        header ={
                   'coinbase': 244687034288125203496486448490407391986876152250L,
                   'difficulty': 256L,
                   'gaslimit': 100000000L,
                   'number': 0L,
                   'timestamp': 1L
                  }
        pos_world = {
                            87579061662017136990230301793909925042452127430L: {
                             'nonce': 0L,
                             'balance': 1000000000000000000L,
                             'code': '`\x08a\x01\x00\na\x01\x00\n`\x00U`\x08`\xff\na\x01\x00\n`\x01U`\x08a\x01\x01\na\x01\x00\n`\x02U`\x08a\x01\x00\n`\xff\n`\x03U`\x08`\xff\n`\xff\n`\x04U`\x08a\x01\x01\n`\xff\n`'\
                             '\x05U`\x08a\x01\x00\na\x01\x01\n`\x06U`\x08`\xff\na\x01\x01\n`\x07U`\x08a\x01\x01\na\x01\x01\n`\x08U',
                             'storage': {
                              3L: 15831402651885036213026743568650891923074156065744116877715268619479738744833L,
                              4L: 88667181452515305589329844365560673397586036248898611545578811096689003725055L,
                              5L: 46877267689434137414103012444013696658268871052188839792194213401121476051199L,
                              6L: 50966202311329169373084543122261872221808286010888550654989201724462468169729L,
                              7L: 5365749204224685697188957744828197388231200721486680577879035665929073066241L,
                              8L: 44602545931516731105551475539355266057143712143472076070568941934099028246785L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=1000000000000000000L, 
                                code='`\x08a\x01\x00\na\x01\x00\n`\x00U`\x08`\xff\na\x01\x00\n`'\
                                     '\x01U`\x08a\x01\x01\na\x01\x00\n`\x02U`\x08a\x01\x00\n`\xff'\
                                     '\n`\x03U`\x08`\xff\n`\xff\n`\x04U`\x08a\x01\x01\n`\xff'\
                                     '\n`\x05U`\x08a\x01\x00\na\x01\x01\n`\x06U`\x08`\xff\na'\
                                     '\x01\x01\n`\x07U`\x08a\x01\x01\na\x01\x01\n`\x08U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069521887415590932569929099639409724315265L
        price = 100000000000000L
        data = ''
        caller = 1170859069521887415590932569929099639409724315265L
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

    def test_smod8_byZero(self):
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
                             'balance': 1000000000000000000L,
                             'code': '`\r`\x00`\xc8`\x00\x03\x07\x03`\x00U',
                             'storage': {
                              0L: 115792089237316195423570985008687907853269984665640564039457584007913129639923L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=1000000000000000000L, 
                                code='`\r`\x00`\xc8`\x00\x03\x07\x03`\x00U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069521887415590932569929099639409724315265L
        price = 100000000000000L
        data = ''
        caller = 1170859069521887415590932569929099639409724315265L
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

    def test_mod2(self):
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
                             'balance': 1000000000000000000L,
                             'code': '\x7f\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff`\x00\x06`\x00U',
                             'storage': {
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=1000000000000000000L, 
                                code='\x7f\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff'\
                                     '\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff`\x00\x06`\x00U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069521887415590932569929099639409724315265L
        price = 100000000000000L
        data = ''
        caller = 1170859069521887415590932569929099639409724315265L
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

    def test_mod3(self):
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
                             'balance': 1000000000000000000L,
                             'code': '`\x00`\x03\x06`\x00U',
                             'storage': {
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=1000000000000000000L, 
                                code='`\x00`\x03\x06`\x00U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069521887415590932569929099639409724315265L
        price = 100000000000000L
        data = ''
        caller = 1170859069521887415590932569929099639409724315265L
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

    def test_mulmod1_overflow3(self):
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
                             'balance': 1000000000000000000L,
                             'code': '`\x05`\x02\x7f\x7f\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\t`\x00U',
                             'storage': {
                              0L: 4L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=1000000000000000000L, 
                                code='`\x05`\x02\x7f\x7f\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff'\
                                     '\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\t`\x00U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069521887415590932569929099639409724315265L
        price = 100000000000000L
        data = ''
        caller = 1170859069521887415590932569929099639409724315265L
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

    def test_mulmod1_overflow2(self):
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
                             'balance': 1000000000000000000L,
                             'code': '`\x05`\x02\x7f\x80\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\t`\x00U',
                             'storage': {
                              0L: 1L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=1000000000000000000L, 
                                code='`\x05`\x02\x7f\x80\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00'\
                                     '\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\t`\x00U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069521887415590932569929099639409724315265L
        price = 100000000000000L
        data = ''
        caller = 1170859069521887415590932569929099639409724315265L
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

    def test_mulmod1_overflow4(self):
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
                             'balance': 1000000000000000000L,
                             'code': '`\x05`\x02\x7f\x80\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x01\t`\x00U',
                             'storage': {
                              0L: 3L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=1000000000000000000L, 
                                code='`\x05`\x02\x7f\x80\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00'\
                                     '\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x01\t`\x00U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069521887415590932569929099639409724315265L
        price = 100000000000000L
        data = ''
        caller = 1170859069521887415590932569929099639409724315265L
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

    def test_signextend_bitIsSet(self):
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
                             'balance': 1000000000000000000L,
                             'code': 'b\x12/\xf4`\x00\x0b`\x00U',
                             'storage': {
                              0L: 115792089237316195423570985008687907853269984665640564039457584007913129639924L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=1000000000000000000L, 
                                code='b\x12/\xf4`\x00\x0b`\x00U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069521887415590932569929099639409724315265L
        price = 100000000000000L
        data = ''
        caller = 1170859069521887415590932569929099639409724315265L
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

    def test_add4(self):
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
                             'balance': 1000000000000000000L,
                             'code': '\x7f\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff`\x01\x01`\x00U',
                             'storage': {
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=1000000000000000000L, 
                                code='\x7f\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff'\
                                     '\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff`\x01\x01`\x00U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069521887415590932569929099639409724315265L
        price = 100000000000000L
        data = ''
        caller = 1170859069521887415590932569929099639409724315265L
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

    def test_add3(self):
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
                             'balance': 1000000000000000000L,
                             'code': '`\x00`\x00\x01`\x00U',
                             'storage': {
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=1000000000000000000L, 
                                code='`\x00`\x00\x01`\x00U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069521887415590932569929099639409724315265L
        price = 100000000000000L
        data = ''
        caller = 1170859069521887415590932569929099639409724315265L
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

    def test_add2(self):
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
                             'balance': 1000000000000000000L,
                             'code': '`\x01\x7f\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\x01`\x00U',
                             'storage': {
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=1000000000000000000L, 
                                code='`\x01\x7f\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff'\
                                     '\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\x01`\x00U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069521887415590932569929099639409724315265L
        price = 100000000000000L
        data = ''
        caller = 1170859069521887415590932569929099639409724315265L
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

    def test_add1(self):
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
                             'balance': 1000000000000000000L,
                             'code': '`\x04\x7f\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\x01`\x00U',
                             'storage': {
                              0L: 3L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=1000000000000000000L, 
                                code='`\x04\x7f\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff'\
                                     '\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\x01`\x00U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069521887415590932569929099639409724315265L
        price = 100000000000000L
        data = ''
        caller = 1170859069521887415590932569929099639409724315265L
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

    def test_add0(self):
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
                             'balance': 1000000000000000000L,
                             'code': '\x7f\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\x7f\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\x01`\x00U',
                             'storage': {
                              0L: 115792089237316195423570985008687907853269984665640564039457584007913129639934L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=1000000000000000000L, 
                                code='\x7f\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff'\
                                     '\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\x7f\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff'\
                                     '\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\x01`\x00'\
                                     'U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069521887415590932569929099639409724315265L
        price = 100000000000000L
        data = ''
        caller = 1170859069521887415590932569929099639409724315265L
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

    def test_sdiv_dejavu(self):
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
                                balance=1000000000000000000L, 
                                code='``\x05``\t``\x00\x03\x05\x80``\x00U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069521887415590932569929099639409724315265L
        price = 1L
        data = ''
        caller = 1170859069521887415590932569929099639409724315265L
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

    def test_sdiv1(self):
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
                             'balance': 1000000000000000000L,
                             'code': '\x7f\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff`\x00\x03\x7f\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\x05`'\
                             '\x00U',
                             'storage': {
                              0L: 115792089237316195423570985008687907853269984665640564039457584007913129639935L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=1000000000000000000L, 
                                code='\x7f\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff'\
                                     '\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff`\x00\x03\x7f\xff\xff\xff\xff\xff\xff\xff\xff\xff'\
                                     '\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff'\
                                     '\x05`\x00U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069521887415590932569929099639409724315265L
        price = 100000000000000L
        data = ''
        caller = 1170859069521887415590932569929099639409724315265L
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

    def test_sdiv0(self):
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
                             'balance': 1000000000000000000L,
                             'code': '\x7f\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\x7f\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff`\x00\x03\x05`'\
                             '\x00U',
                             'storage': {
                              0L: 115792089237316195423570985008687907853269984665640564039457584007913129639935L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=1000000000000000000L, 
                                code='\x7f\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff'\
                                     '\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\x7f\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff'\
                                     '\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff`\x00\x03'\
                                     '\x05`\x00U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069521887415590932569929099639409724315265L
        price = 100000000000000L
        data = ''
        caller = 1170859069521887415590932569929099639409724315265L
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

    def test_sdiv3(self):
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
                             'balance': 1000000000000000000L,
                             'code': '`\x02`\x00\x03`\x04\x05`\x00U',
                             'storage': {
                              0L: 115792089237316195423570985008687907853269984665640564039457584007913129639934L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=1000000000000000000L, 
                                code='`\x02`\x00\x03`\x04\x05`\x00U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069521887415590932569929099639409724315265L
        price = 100000000000000L
        data = ''
        caller = 1170859069521887415590932569929099639409724315265L
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

    def test_sdiv2(self):
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
                             'balance': 1000000000000000000L,
                             'code': '`\x04`\x00\x03`\x02`\x00\x03\x05`\x00U',
                             'storage': {
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=1000000000000000000L, 
                                code='`\x04`\x00\x03`\x02`\x00\x03\x05`\x00U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069521887415590932569929099639409724315265L
        price = 100000000000000L
        data = ''
        caller = 1170859069521887415590932569929099639409724315265L
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

    def test_sdiv5(self):
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
                             'balance': 1000000000000000000L,
                             'code': '`\x01`\x00\x03\x7f\x80\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00`\x00\x03\x05`\x00U',
                             'storage': {
                              0L: 57896044618658097711785492504343953926634992332820282019728792003956564819968L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=1000000000000000000L, 
                                code='`\x01`\x00\x03\x7f\x80\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00'\
                                     '\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00`\x00\x03\x05`\x00U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069521887415590932569929099639409724315265L
        price = 100000000000000L
        data = ''
        caller = 1170859069521887415590932569929099639409724315265L
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

    def test_sdiv4(self):
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
                             'balance': 1000000000000000000L,
                             'code': '`\x04`\x00\x03`\x05\x05`\x00U',
                             'storage': {
                              0L: 115792089237316195423570985008687907853269984665640564039457584007913129639935L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=1000000000000000000L, 
                                code='`\x04`\x00\x03`\x05\x05`\x00U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069521887415590932569929099639409724315265L
        price = 100000000000000L
        data = ''
        caller = 1170859069521887415590932569929099639409724315265L
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

    def test_sdiv7(self):
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
                             'balance': 1000000000000000000L,
                             'code': '`\x19`\x01`\x00\x03\x05`\x00U',
                             'storage': {
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=1000000000000000000L, 
                                code='`\x19`\x01`\x00\x03\x05`\x00U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069521887415590932569929099639409724315265L
        price = 100000000000000L
        data = ''
        caller = 1170859069521887415590932569929099639409724315265L
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

    def test_sdiv6(self):
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
                             'balance': 1000000000000000000L,
                             'code': '`\x00\x7f\x80\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00`\x00\x03\x05`\x00U',
                             'storage': {
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=1000000000000000000L, 
                                code='`\x00\x7f\x80\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00'\
                                     '\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00`\x00\x03\x05`\x00U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069521887415590932569929099639409724315265L
        price = 100000000000000L
        data = ''
        caller = 1170859069521887415590932569929099639409724315265L
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

    def test_sdiv9(self):
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
                             'balance': 1000000000000000000L,
                             'code': '`\x01`\x01`\x00\x03\x05`\x00U',
                             'storage': {
                              0L: 115792089237316195423570985008687907853269984665640564039457584007913129639935L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=1000000000000000000L, 
                                code='`\x01`\x01`\x00\x03\x05`\x00U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069521887415590932569929099639409724315265L
        price = 100000000000000L
        data = ''
        caller = 1170859069521887415590932569929099639409724315265L
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

    def test_sdiv8(self):
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
                             'balance': 1000000000000000000L,
                             'code': '`\x01`\x00\x03`\x01`\x00\x03\x05`\x00U',
                             'storage': {
                              0L: 1L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=1000000000000000000L, 
                                code='`\x01`\x00\x03`\x01`\x00\x03\x05`\x00U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069521887415590932569929099639409724315265L
        price = 100000000000000L
        data = ''
        caller = 1170859069521887415590932569929099639409724315265L
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

    def test_signextend_BitIsNotSetInHigherByte(self):
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
                             'balance': 1000000000000000000L,
                             'code': 'b\x12j\xf4`\x01\x0b`\x00U',
                             'storage': {
                              0L: 27380L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=1000000000000000000L, 
                                code='b\x12j\xf4`\x01\x0b`\x00U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069521887415590932569929099639409724315265L
        price = 100000000000000L
        data = ''
        caller = 1170859069521887415590932569929099639409724315265L
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

    def test_addmod1_overflowDiff(self):
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
                             'balance': 1000000000000000000L,
                             'code': '`\x05`\x02`\x00\x03`\x01`\x00\x03\x08`\x00U',
                             'storage': {
                              0L: 4L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=1000000000000000000L, 
                                code='`\x05`\x02`\x00\x03`\x01`\x00\x03\x08`\x00U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069521887415590932569929099639409724315265L
        price = 100000000000000L
        data = ''
        caller = 1170859069521887415590932569929099639409724315265L
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

    def test_expPowerOf2_32(self):
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
                             'balance': 1000000000000000000L,
                             'code': '` `\x02\n`\x00U`\x1f`\x02\n`\x01U`!`\x02\n`\x02U',
                             'storage': {
                              0L: 4294967296L,
                              1L: 2147483648L,
                              2L: 8589934592L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=1000000000000000000L, 
                                code='` `\x02\n`\x00U`\x1f`\x02\n`\x01U`!`\x02\n`\x02'\
                                     'U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069521887415590932569929099639409724315265L
        price = 100000000000000L
        data = ''
        caller = 1170859069521887415590932569929099639409724315265L
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

    def test_stop(self):
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
                             'balance': 1000000000000000000L,
                             'code': '\x00',
                             'storage': {
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=1000000000000000000L, 
                                code='\x00', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069521887415590932569929099639409724315265L
        price = 100000000000000L
        data = ''
        caller = 1170859069521887415590932569929099639409724315265L
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

    def test_addmod3_0(self):
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
                             'balance': 1000000000000000000L,
                             'code': '`\x02`\x03`\x00\x03`\x01`\x04\x08\x14`\x00U',
                             'storage': {
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=1000000000000000000L, 
                                code='`\x02`\x03`\x00\x03`\x01`\x04\x08\x14`\x00U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069521887415590932569929099639409724315265L
        price = 100000000000000L
        data = ''
        caller = 1170859069521887415590932569929099639409724315265L
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

    def test_mulmod2_0(self):
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
                             'balance': 1000000000000000000L,
                             'code': '`\x03`\x01`\x05`\x00\x03\t`\x03`\x05`\x00\x03\x07\x14`\x00U',
                             'storage': {
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=1000000000000000000L, 
                                code='`\x03`\x01`\x05`\x00\x03\t`\x03`\x05`\x00\x03\x07\x14`\x00U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069521887415590932569929099639409724315265L
        price = 100000000000000L
        data = ''
        caller = 1170859069521887415590932569929099639409724315265L
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

    def test_mulmod2_1(self):
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
                             'balance': 1000000000000000000L,
                             'code': '`\x03`\x01`\x05`\x00\x03\t`\x03`\x05`\x00\x03\x06\x14`\x00U',
                             'storage': {
                              0L: 1L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=1000000000000000000L, 
                                code='`\x03`\x01`\x05`\x00\x03\t`\x03`\x05`\x00\x03\x06\x14`\x00U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069521887415590932569929099639409724315265L
        price = 100000000000000L
        data = ''
        caller = 1170859069521887415590932569929099639409724315265L
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

    def test_signextend_Overflow_dj42(self):
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
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=1000000000000000000L, 
                                code='`\x05V', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069521887415590932569929099639409724315265L
        price = 100000000000000L
        data = ''
        caller = 1170859069521887415590932569929099639409724315265L
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

    def test_expPowerOf256Of256_33(self):
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
                             'balance': 1000000000000000000L,
                             'code': '`!a\x01\x00\na\x01\x00\n`\x00U`!`\xff\na\x01\x00\n`\x01U`!a\x01\x01\na\x01\x00\n`\x02U`!a\x01\x00\n`\xff\n`\x03U`!`\xff\n`\xff\n`\x04U`!a\x01\x01\n`\xff\n`'\
                             '\x05U`!a\x01\x00\na\x01\x01\n`\x06U`!`\xff\na\x01\x01\n`\x07U`!a\x01\x01\na\x01\x01\n`\x08U',
                             'storage': {
                              0L: 1L,
                              3L: 1L,
                              4L: 64135483568242129660189811524440266649397055745562313858450489812292508581631L,
                              5L: 46398695887435477574305959260606258506859266453477299410648234630417678926079L,
                              6L: 1L,
                              7L: 104245036966221287026270471239637571306194808795660508680275132968035193847553L,
                              8L: 26104390486839708587903636031676095792383620198177622282435444888970572398849L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=1000000000000000000L, 
                                code='`!a\x01\x00\na\x01\x00\n`\x00U`!`\xff\na\x01\x00\n`'\
                                     '\x01U`!a\x01\x01\na\x01\x00\n`\x02U`!a\x01\x00\n`\xff'\
                                     '\n`\x03U`!`\xff\n`\xff\n`\x04U`!a\x01\x01\n`\xff'\
                                     '\n`\x05U`!a\x01\x00\na\x01\x01\n`\x06U`!`\xff\na'\
                                     '\x01\x01\n`\x07U`!a\x01\x01\na\x01\x01\n`\x08U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069521887415590932569929099639409724315265L
        price = 100000000000000L
        data = ''
        caller = 1170859069521887415590932569929099639409724315265L
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

    def test_expPowerOf256Of256_32(self):
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
                             'balance': 1000000000000000000L,
                             'code': '` a\x01\x00\na\x01\x00\n`\x00U` `\xff\na\x01\x00\n`\x01U` a\x01\x01\na\x01\x00\n`\x02U` a\x01\x00\n`\xff\n`\x03U` `\xff\n`\xff\n`\x04U` a\x01\x01\n`\xff\n`'\
                             '\x05U` a\x01\x00\na\x01\x01\n`\x06U` `\xff\na\x01\x01\n`\x07U` a\x01\x01\na\x01\x01\n`\x08U',
                             'storage': {
                              0L: 1L,
                              3L: 1L,
                              4L: 83290000642302749123389682511803062288674053658743011274318334092251811021055L,
                              5L: 107796101041354274209995467705717706987961056180087872912716600609070003519743L,
                              6L: 1L,
                              7L: 107494645127108603178874279381187166621140539703347472922785670214454066807041L,
                              8L: 36720049077504322823338175525090117350613636142111226285606247996852040368385L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=1000000000000000000L, 
                                code='` a\x01\x00\na\x01\x00\n`\x00U` `\xff\na\x01\x00\n`'\
                                     '\x01U` a\x01\x01\na\x01\x00\n`\x02U` a\x01\x00\n`\xff'\
                                     '\n`\x03U` `\xff\n`\xff\n`\x04U` a\x01\x01\n`\xff'\
                                     '\n`\x05U` a\x01\x00\na\x01\x01\n`\x06U` `\xff\na'\
                                     '\x01\x01\n`\x07U` a\x01\x01\na\x01\x01\n`\x08U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069521887415590932569929099639409724315265L
        price = 100000000000000L
        data = ''
        caller = 1170859069521887415590932569929099639409724315265L
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

    def test_expPowerOf256Of256_31(self):
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
                             'balance': 1000000000000000000L,
                             'code': '`\x1fa\x01\x00\na\x01\x00\n`\x00U`\x1f`\xff\na\x01\x00\n`\x01U`\x1fa\x01\x01\na\x01\x00\n`\x02U`\x1fa\x01\x00\n`\xff\n`\x03U`\x1f`\xff\n`\xff\n`\x04U`\x1fa\x01\x01\n`\xff\n`'\
                             '\x05U`\x1fa\x01\x00\na\x01\x01\n`\x06U`\x1f`\xff\na\x01\x01\n`\x07U`\x1fa\x01\x01\na\x01\x01\n`\x08U',
                             'storage': {
                              3L: 1L,
                              4L: 112985507611037855861351294922934055679136269367323143362415325409413936578303L,
                              5L: 62075428888398948475210828438627792272695349249636165883831517298362121388287L,
                              6L: 1L,
                              7L: 107818586060941895166288682821279836433776680519631913166930934049164849315585L,
                              8L: 81761461417135675039681145207874119897008583353196969206846550448999168409857L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=1000000000000000000L, 
                                code='`\x1fa\x01\x00\na\x01\x00\n`\x00U`\x1f`\xff\na\x01\x00\n`'\
                                     '\x01U`\x1fa\x01\x01\na\x01\x00\n`\x02U`\x1fa\x01\x00\n`\xff'\
                                     '\n`\x03U`\x1f`\xff\n`\xff\n`\x04U`\x1fa\x01\x01\n`\xff'\
                                     '\n`\x05U`\x1fa\x01\x00\na\x01\x01\n`\x06U`\x1f`\xff\na'\
                                     '\x01\x01\n`\x07U`\x1fa\x01\x01\na\x01\x01\n`\x08U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069521887415590932569929099639409724315265L
        price = 100000000000000L
        data = ''
        caller = 1170859069521887415590932569929099639409724315265L
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

    def test_expPowerOf256Of256_30(self):
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
                             'balance': 1000000000000000000L,
                             'code': '`\x1ea\x01\x00\na\x01\x00\n`\x00U`\x1e`\xff\na\x01\x00\n`\x01U`\x1ea\x01\x01\na\x01\x00\n`\x02U`\x1ea\x01\x00\n`\xff\n`\x03U`\x1e`\xff\n`\xff\n`\x04U`\x1ea\x01\x01\n`\xff\n`'\
                             '\x05U`\x1ea\x01\x00\na\x01\x01\n`\x06U`\x1e`\xff\na\x01\x01\n`\x07U`\x1ea\x01\x01\na\x01\x01\n`\x08U',
                             'storage': {
                              3L: 57443731770074831323412168344153766786583156455220123566449660816425654157313L,
                              4L: 105599420949718761373086994757860478259024540739650663766696805544756942864639L,
                              5L: 23492387631362241410954083125785775807737875757943251864054532318400312377599L,
                              6L: 58348357467241364100158816664534141066686828210420440473007923191487475482625L,
                              7L: 114548869433232456914198824234733305079953169742594190201731254450200934220033L,
                              8L: 89404147834226705822834044214734168223325601657396406432574474219566049132801L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=1000000000000000000L, 
                                code='`\x1ea\x01\x00\na\x01\x00\n`\x00U`\x1e`\xff\na\x01\x00\n`'\
                                     '\x01U`\x1ea\x01\x01\na\x01\x00\n`\x02U`\x1ea\x01\x00\n`\xff'\
                                     '\n`\x03U`\x1e`\xff\n`\xff\n`\x04U`\x1ea\x01\x01\n`\xff'\
                                     '\n`\x05U`\x1ea\x01\x00\na\x01\x01\n`\x06U`\x1e`\xff\na'\
                                     '\x01\x01\n`\x07U`\x1ea\x01\x01\na\x01\x01\n`\x08U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069521887415590932569929099639409724315265L
        price = 100000000000000L
        data = ''
        caller = 1170859069521887415590932569929099639409724315265L
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

    def test_exp3(self):
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
                             'balance': 1000000000000000000L,
                             'code': 'c\x7f\xff\xff\xff`\x00\n`\x00U',
                             'storage': {
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=1000000000000000000L, 
                                code='c\x7f\xff\xff\xff`\x00\n`\x00U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069521887415590932569929099639409724315265L
        price = 100000000000000L
        data = ''
        caller = 1170859069521887415590932569929099639409724315265L
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

    def test_exp2(self):
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
                             'balance': 1000000000000000000L,
                             'code': 'c\x7f\xff\xff\xffc\x7f\xff\xff\xff\n`\x00U',
                             'storage': {
                              0L: 85283587600373122322928310453130164142775440871555374690023406742016433848319L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=1000000000000000000L, 
                                code='c\x7f\xff\xff\xffc\x7f\xff\xff\xff\n`\x00U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069521887415590932569929099639409724315265L
        price = 100000000000000L
        data = ''
        caller = 1170859069521887415590932569929099639409724315265L
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

    def test_exp1(self):
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
                             'balance': 1000000000000000000L,
                             'code': '\x7f\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xfe\x7f\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\n`\x00U',
                             'storage': {
                              0L: 1L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=1000000000000000000L, 
                                code='\x7f\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff'\
                                     '\xff\xff\xff\xff\xff\xff\xff\xff\xff\xfe\x7f\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff'\
                                     '\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\n`\x00'\
                                     'U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069521887415590932569929099639409724315265L
        price = 100000000000000L
        data = ''
        caller = 1170859069521887415590932569929099639409724315265L
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

    def test_exp0(self):
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
                             'balance': 1000000000000000000L,
                             'code': '`\x02`\x02\n`\x00U',
                             'storage': {
                              0L: 4L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=1000000000000000000L, 
                                code='`\x02`\x02\n`\x00U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069521887415590932569929099639409724315265L
        price = 100000000000000L
        data = ''
        caller = 1170859069521887415590932569929099639409724315265L
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

    def test_exp7(self):
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
                             'balance': 1000000000000000000L,
                             'code': 'a\x01\x01`\x02\n`\x00U',
                             'storage': {
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=1000000000000000000L, 
                                code='a\x01\x01`\x02\n`\x00U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069521887415590932569929099639409724315265L
        price = 100000000000000L
        data = ''
        caller = 1170859069521887415590932569929099639409724315265L
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

    def test_exp6(self):
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
                             'balance': 1000000000000000000L,
                             'code': 'a\x01\x01`\x01\n`\x00U',
                             'storage': {
                              0L: 1L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=1000000000000000000L, 
                                code='a\x01\x01`\x01\n`\x00U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069521887415590932569929099639409724315265L
        price = 100000000000000L
        data = ''
        caller = 1170859069521887415590932569929099639409724315265L
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

    def test_exp5(self):
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
                             'balance': 1000000000000000000L,
                             'code': '`\x01a\x01\x01\n`\x00U',
                             'storage': {
                              0L: 257L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=1000000000000000000L, 
                                code='`\x01a\x01\x01\n`\x00U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069521887415590932569929099639409724315265L
        price = 100000000000000L
        data = ''
        caller = 1170859069521887415590932569929099639409724315265L
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

    def test_exp4(self):
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
                             'balance': 1000000000000000000L,
                             'code': '`\x00c\x7f\xff\xff\xff\n`\x00U',
                             'storage': {
                              0L: 1L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=1000000000000000000L, 
                                code='`\x00c\x7f\xff\xff\xff\n`\x00U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069521887415590932569929099639409724315265L
        price = 100000000000000L
        data = ''
        caller = 1170859069521887415590932569929099639409724315265L
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

    def test_mulmod4(self):
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
                             'balance': 1000000000000000000L,
                             'code': '`d`\x1b`%\t`\x00S`\x00`\x01\xf3',
                             'storage': {
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=1000000000000000000L, 
                                code='`d`\x1b`%\t`\x00S`\x00`\x01\xf3', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069521887415590932569929099639409724315265L
        price = 100000000000000L
        data = ''
        caller = 1170859069521887415590932569929099639409724315265L
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

    def test_mulmod1(self):
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
                             'balance': 1000000000000000000L,
                             'code': '`\x03`\x02`\x00\x03`\x01`\x00\x03\t`\x00U',
                             'storage': {
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=1000000000000000000L, 
                                code='`\x03`\x02`\x00\x03`\x01`\x00\x03\t`\x00U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069521887415590932569929099639409724315265L
        price = 100000000000000L
        data = ''
        caller = 1170859069521887415590932569929099639409724315265L
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

    def test_mulmod0(self):
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
                             'balance': 1000000000000000000L,
                             'code': '`\x02`\x02`\x01\t`\x00U',
                             'storage': {
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=1000000000000000000L, 
                                code='`\x02`\x02`\x01\t`\x00U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069521887415590932569929099639409724315265L
        price = 100000000000000L
        data = ''
        caller = 1170859069521887415590932569929099639409724315265L
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

    def test_mulmod3(self):
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
                             'balance': 1000000000000000000L,
                             'code': '`\x03`\x00\x03`\x01`\x05\t`\x00U',
                             'storage': {
                              0L: 5L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=1000000000000000000L, 
                                code='`\x03`\x00\x03`\x01`\x05\t`\x00U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069521887415590932569929099639409724315265L
        price = 100000000000000L
        data = ''
        caller = 1170859069521887415590932569929099639409724315265L
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

    def test_mulmod2(self):
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
                             'balance': 1000000000000000000L,
                             'code': '`\x03`\x01`\x05`\x00\x03\t`\x00U',
                             'storage': {
                              0L: 2L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=1000000000000000000L, 
                                code='`\x03`\x01`\x05`\x00\x03\t`\x00U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069521887415590932569929099639409724315265L
        price = 100000000000000L
        data = ''
        caller = 1170859069521887415590932569929099639409724315265L
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

    def test_signextend_BitIsNotSet(self):
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
                             'balance': 1000000000000000000L,
                             'code': 'b\x12/j`\x00\x0b`\x00U',
                             'storage': {
                              0L: 106L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=1000000000000000000L, 
                                code='b\x12/j`\x00\x0b`\x00U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069521887415590932569929099639409724315265L
        price = 100000000000000L
        data = ''
        caller = 1170859069521887415590932569929099639409724315265L
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

    def test_smod2(self):
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
                             'balance': 1000000000000000000L,
                             'code': '`\x03`\x05`\x00\x03\x07`\x00U',
                             'storage': {
                              0L: 115792089237316195423570985008687907853269984665640564039457584007913129639934L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=1000000000000000000L, 
                                code='`\x03`\x05`\x00\x03\x07`\x00U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069521887415590932569929099639409724315265L
        price = 100000000000000L
        data = ''
        caller = 1170859069521887415590932569929099639409724315265L
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

    def test_smod3(self):
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
                             'balance': 1000000000000000000L,
                             'code': '\x7f\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff`\x02`\x00\x03\x07`\x00U',
                             'storage': {
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=1000000000000000000L, 
                                code='\x7f\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff'\
                                     '\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff`\x02`\x00\x03\x07`\x00U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069521887415590932569929099639409724315265L
        price = 100000000000000L
        data = ''
        caller = 1170859069521887415590932569929099639409724315265L
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

    def test_smod0(self):
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
                             'balance': 1000000000000000000L,
                             'code': '`\x03`\x00\x03`\x05`\x00\x03\x07`\x00U',
                             'storage': {
                              0L: 115792089237316195423570985008687907853269984665640564039457584007913129639934L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=1000000000000000000L, 
                                code='`\x03`\x00\x03`\x05`\x00\x03\x07`\x00U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069521887415590932569929099639409724315265L
        price = 100000000000000L
        data = ''
        caller = 1170859069521887415590932569929099639409724315265L
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

    def test_smod1(self):
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
                             'balance': 1000000000000000000L,
                             'code': '`\x03`\x00\x03`\x05\x07`\x00U',
                             'storage': {
                              0L: 2L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=1000000000000000000L, 
                                code='`\x03`\x00\x03`\x05\x07`\x00U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069521887415590932569929099639409724315265L
        price = 100000000000000L
        data = ''
        caller = 1170859069521887415590932569929099639409724315265L
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

    def test_smod6(self):
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
                             'balance': 1000000000000000000L,
                             'code': '\x7f\x7f\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\x7f\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff`\x00\x03\x07`'\
                             '\x00U',
                             'storage': {
                              0L: 1L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=1000000000000000000L, 
                                code='\x7f\x7f\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff'\
                                     '\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\x7f\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff'\
                                     '\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff`\x00\x03'\
                                     '\x07`\x00U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069521887415590932569929099639409724315265L
        price = 100000000000000L
        data = ''
        caller = 1170859069521887415590932569929099639409724315265L
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

    def test_sub3(self):
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
                             'balance': 1000000000000000000L,
                             'code': '\x7f\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff`\x00\x03`\x00U',
                             'storage': {
                              0L: 1L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=1000000000000000000L, 
                                code='\x7f\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff'\
                                     '\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff`\x00\x03`\x00U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069521887415590932569929099639409724315265L
        price = 100000000000000L
        data = ''
        caller = 1170859069521887415590932569929099639409724315265L
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

    def test_smod4(self):
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
                             'balance': 1000000000000000000L,
                             'code': '`\x00`\x02`\x00\x03\x07`\x00U',
                             'storage': {
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=1000000000000000000L, 
                                code='`\x00`\x02`\x00\x03\x07`\x00U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069521887415590932569929099639409724315265L
        price = 100000000000000L
        data = ''
        caller = 1170859069521887415590932569929099639409724315265L
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

    def test_smod5(self):
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
                             'balance': 1000000000000000000L,
                             'code': '\x7f\x7f\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\x7f\x7f\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff`\x00\x03\x07`'\
                             '\x00U',
                             'storage': {
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=1000000000000000000L, 
                                code='\x7f\x7f\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff'\
                                     '\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\x7f\x7f\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff'\
                                     '\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff`\x00\x03'\
                                     '\x07`\x00U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069521887415590932569929099639409724315265L
        price = 100000000000000L
        data = ''
        caller = 1170859069521887415590932569929099639409724315265L
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

    def test_signextend_bigBytePlus1(self):
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
                             'balance': 1000000000000000000L,
                             'code': 'f\xf0\x00\x00\x00\x00\x00\x01a\xff\xff\x0b`\x00U',
                             'storage': {
                              0L: 67553994410557441L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=1000000000000000000L, 
                                code='f\xf0\x00\x00\x00\x00\x00\x01a\xff\xff\x0b`\x00U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069521887415590932569929099639409724315265L
        price = 100000000000000L
        data = ''
        caller = 1170859069521887415590932569929099639409724315265L
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

    def test_addmodDivByZero3(self):
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
                             'balance': 1000000000000000000L,
                             'code': '`\x01`\x00`\x00`\x00\x08\x03`\x00U',
                             'storage': {
                              0L: 115792089237316195423570985008687907853269984665640564039457584007913129639935L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=1000000000000000000L, 
                                code='`\x01`\x00`\x00`\x00\x08\x03`\x00U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069521887415590932569929099639409724315265L
        price = 100000000000000L
        data = ''
        caller = 1170859069521887415590932569929099639409724315265L
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

    def test_addmodDivByZero2(self):
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
                             'balance': 1000000000000000000L,
                             'code': '`\x00`\x00`\x01\x08`\x00U',
                             'storage': {
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=1000000000000000000L, 
                                code='`\x00`\x00`\x01\x08`\x00U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069521887415590932569929099639409724315265L
        price = 100000000000000L
        data = ''
        caller = 1170859069521887415590932569929099639409724315265L
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

    def test_expPowerOf2_128(self):
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
                             'balance': 1000000000000000000L,
                             'code': '`\x80`\x02\n`\x00U`\x7f`\x02\n`\x01U`\x81`\x02\n`\x02U',
                             'storage': {
                              0L: 340282366920938463463374607431768211456L,
                              1L: 170141183460469231731687303715884105728L,
                              2L: 680564733841876926926749214863536422912L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=1000000000000000000L, 
                                code='`\x80`\x02\n`\x00U`\x7f`\x02\n`\x01U`\x81`\x02\n`\x02'\
                                     'U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069521887415590932569929099639409724315265L
        price = 100000000000000L
        data = ''
        caller = 1170859069521887415590932569929099639409724315265L
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

    def test_expPowerOf256Of256_25(self):
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
                             'balance': 1000000000000000000L,
                             'code': '`\x19a\x01\x00\na\x01\x00\n`\x00U`\x19`\xff\na\x01\x00\n`\x01U`\x19a\x01\x01\na\x01\x00\n`\x02U`\x19a\x01\x00\n`\xff\n`\x03U`\x19`\xff\n`\xff\n`\x04U`\x19a\x01\x01\n`\xff\n`'\
                             '\x05U`\x19a\x01\x00\na\x01\x01\n`\x06U`\x19`\xff\na\x01\x01\n`\x07U`\x19a\x01\x01\na\x01\x01\n`\x08U',
                             'storage': {
                              3L: 23082677268810102567787957297101600109208477565640060193443191380828630286337L,
                              4L: 57586941904103598579764390844964981043049052155114937185797634212581688737535L,
                              5L: 8349948914438381240675947491016368716939310261807744693247618018857855811839L,
                              6L: 15363911409789054756994145414988457629001175372500027154689132866782353162241L,
                              7L: 46259949032879378200402632411429142790698144536296724901325017870796521602817L,
                              8L: 18926565843436435145785316737060988839741893259630947091482933154404627972353L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=1000000000000000000L, 
                                code='`\x19a\x01\x00\na\x01\x00\n`\x00U`\x19`\xff\na\x01\x00\n`'\
                                     '\x01U`\x19a\x01\x01\na\x01\x00\n`\x02U`\x19a\x01\x00\n`\xff'\
                                     '\n`\x03U`\x19`\xff\n`\xff\n`\x04U`\x19a\x01\x01\n`\xff'\
                                     '\n`\x05U`\x19a\x01\x00\na\x01\x01\n`\x06U`\x19`\xff\na'\
                                     '\x01\x01\n`\x07U`\x19a\x01\x01\na\x01\x01\n`\x08U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069521887415590932569929099639409724315265L
        price = 100000000000000L
        data = ''
        caller = 1170859069521887415590932569929099639409724315265L
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

    def test_expPowerOf256Of256_20(self):
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
                             'balance': 1000000000000000000L,
                             'code': '`\x14a\x01\x00\na\x01\x00\n`\x00U`\x14`\xff\na\x01\x00\n`\x01U`\x14a\x01\x01\na\x01\x00\n`\x02U`\x14a\x01\x00\n`\xff\n`\x03U`\x14`\xff\n`\xff\n`\x04U`\x14a\x01\x01\n`\xff\n`'\
                             '\x05U`\x14a\x01\x00\na\x01\x01\n`\x06U`\x14`\xff\na\x01\x01\n`\x07U`\x14a\x01\x01\na\x01\x01\n`\x08U',
                             'storage': {
                              3L: 11095128516485485949393957618129868380154060907080998068241024442132250755073L,
                              4L: 46991903036590546434450396132155379898382754470087505882848419300294039175423L,
                              5L: 73186518788354931992268309607910110463491507624599205551010472211597684375807L,
                              6L: 108556343652588169849457393533512576632030094861390478212741088232779389337601L,
                              7L: 92676439589099754655655035309645792128747303076858301322675459756614409257217L,
                              8L: 26768014775117825313334555689265921696132636065691461838850023344632663113985L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=1000000000000000000L, 
                                code='`\x14a\x01\x00\na\x01\x00\n`\x00U`\x14`\xff\na\x01\x00\n`'\
                                     '\x01U`\x14a\x01\x01\na\x01\x00\n`\x02U`\x14a\x01\x00\n`\xff'\
                                     '\n`\x03U`\x14`\xff\n`\xff\n`\x04U`\x14a\x01\x01\n`\xff'\
                                     '\n`\x05U`\x14a\x01\x00\na\x01\x01\n`\x06U`\x14`\xff\na'\
                                     '\x01\x01\n`\x07U`\x14a\x01\x01\na\x01\x01\n`\x08U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069521887415590932569929099639409724315265L
        price = 100000000000000L
        data = ''
        caller = 1170859069521887415590932569929099639409724315265L
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

    def test_expPowerOf256Of256_21(self):
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
                             'balance': 1000000000000000000L,
                             'code': '`\x15a\x01\x00\na\x01\x00\n`\x00U`\x15`\xff\na\x01\x00\n`\x01U`\x15a\x01\x01\na\x01\x00\n`\x02U`\x15a\x01\x00\n`\xff\n`\x03U`\x15`\xff\n`\xff\n`\x04U`\x15a\x01\x01\n`\xff\n`'\
                             '\x05U`\x15a\x01\x00\na\x01\x01\n`\x06U`\x15`\xff\na\x01\x01\n`\x07U`\x15a\x01\x01\na\x01\x01\n`\x08U',
                             'storage': {
                              3L: 61342758524695712879149510032736516840959960237361968522720240995941081939969L,
                              4L: 57812011273622918000071749720687928256516815605767307141354861404086017982207L,
                              5L: 46296291811536365292556049945344103552150633476469514979425859868512526598399L,
                              6L: 322558106684579804056342494121733014907964762227052991898425692372556840961L,
                              7L: 12926000559402174768074498440631375790110453153840292162623164820974892089089L,
                              8L: 32708451558369615005306371218201330517589418479369948923109316077262889877761L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=1000000000000000000L, 
                                code='`\x15a\x01\x00\na\x01\x00\n`\x00U`\x15`\xff\na\x01\x00\n`'\
                                     '\x01U`\x15a\x01\x01\na\x01\x00\n`\x02U`\x15a\x01\x00\n`\xff'\
                                     '\n`\x03U`\x15`\xff\n`\xff\n`\x04U`\x15a\x01\x01\n`\xff'\
                                     '\n`\x05U`\x15a\x01\x00\na\x01\x01\n`\x06U`\x15`\xff\na'\
                                     '\x01\x01\n`\x07U`\x15a\x01\x01\na\x01\x01\n`\x08U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069521887415590932569929099639409724315265L
        price = 100000000000000L
        data = ''
        caller = 1170859069521887415590932569929099639409724315265L
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

    def test_expPowerOf256Of256_22(self):
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
                             'balance': 1000000000000000000L,
                             'code': '`\x16a\x01\x00\na\x01\x00\n`\x00U`\x16`\xff\na\x01\x00\n`\x01U`\x16a\x01\x01\na\x01\x00\n`\x02U`\x16a\x01\x00\n`\xff\n`\x03U`\x16`\xff\n`\xff\n`\x04U`\x16a\x01\x01\n`\xff\n`'\
                             '\x05U`\x16a\x01\x00\na\x01\x01\n`\x06U`\x16`\xff\na\x01\x01\n`\x07U`\x16a\x01\x01\na\x01\x01\n`\x08U',
                             'storage': {
                              3L: 71814135284416114880191592207680751094301890903187796489607853892644475240449L,
                              4L: 106866850240512374621662861338623158047087776162904039993394603528705656094975L,
                              5L: 99765853430484146798068180455785111509035460348020690374049778250251620450559L,
                              6L: 82574875311252429838423678495163651816438979130125565925996977247374551285761L,
                              7L: 99934025607600089733745581488993139205016396189826818067336339035974376489217L,
                              8L: 35007363591506868599869923830536024009816445536217041298284962531613703799041L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=1000000000000000000L, 
                                code='`\x16a\x01\x00\na\x01\x00\n`\x00U`\x16`\xff\na\x01\x00\n`'\
                                     '\x01U`\x16a\x01\x01\na\x01\x00\n`\x02U`\x16a\x01\x00\n`\xff'\
                                     '\n`\x03U`\x16`\xff\n`\xff\n`\x04U`\x16a\x01\x01\n`\xff'\
                                     '\n`\x05U`\x16a\x01\x00\na\x01\x01\n`\x06U`\x16`\xff\na'\
                                     '\x01\x01\n`\x07U`\x16a\x01\x01\na\x01\x01\n`\x08U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069521887415590932569929099639409724315265L
        price = 100000000000000L
        data = ''
        caller = 1170859069521887415590932569929099639409724315265L
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

    def test_expPowerOf256Of256_23(self):
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
                             'balance': 1000000000000000000L,
                             'code': '`\x17a\x01\x00\na\x01\x00\n`\x00U`\x17`\xff\na\x01\x00\n`\x01U`\x17a\x01\x01\na\x01\x00\n`\x02U`\x17a\x01\x00\n`\xff\n`\x03U`\x17`\xff\n`\xff\n`\x04U`\x17a\x01\x01\n`\xff\n`'\
                             '\x05U`\x17a\x01\x00\na\x01\x01\n`\x06U`\x17`\xff\na\x01\x01\n`\x07U`\x17a\x01\x01\na\x01\x01\n`\x08U',
                             'storage': {
                              3L: 89268533314566532404831973793582839324626494044866783105312323266711178444801L,
                              4L: 37762166224943216354061133881990828131179932191099912485812863065457132175103L,
                              5L: 60725702600970256357882219932341380643608066257735113198817913599684720918783L,
                              6L: 65007838489074471546542423180695635713241448165562221873945885887695534686209L,
                              7L: 39191009359259173528470521365271419600056804692268038397265417242355032391425L,
                              8L: 38838507269272866444318461020062831438059409336168580428448728650033864835329L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=1000000000000000000L, 
                                code='`\x17a\x01\x00\na\x01\x00\n`\x00U`\x17`\xff\na\x01\x00\n`'\
                                     '\x01U`\x17a\x01\x01\na\x01\x00\n`\x02U`\x17a\x01\x00\n`\xff'\
                                     '\n`\x03U`\x17`\xff\n`\xff\n`\x04U`\x17a\x01\x01\n`\xff'\
                                     '\n`\x05U`\x17a\x01\x00\na\x01\x01\n`\x06U`\x17`\xff\na'\
                                     '\x01\x01\n`\x07U`\x17a\x01\x01\na\x01\x01\n`\x08U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069521887415590932569929099639409724315265L
        price = 100000000000000L
        data = ''
        caller = 1170859069521887415590932569929099639409724315265L
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

    def test_expPowerOf256Of256_24(self):
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
                             'balance': 1000000000000000000L,
                             'code': '`\x18a\x01\x00\na\x01\x00\n`\x00U`\x18`\xff\na\x01\x00\n`\x01U`\x18a\x01\x01\na\x01\x00\n`\x02U`\x18a\x01\x00\n`\xff\n`\x03U`\x18`\xff\n`\xff\n`\x04U`\x18a\x01\x01\n`\xff\n`'\
                             '\x05U`\x18a\x01\x00\na\x01\x01\n`\x06U`\x18`\xff\na\x01\x01\n`\x07U`\x18a\x01\x01\na\x01\x01\n`\x08U',
                             'storage': {
                              3L: 41702948777741797193501244445689020010195496354705359186810706719175142801409L,
                              4L: 96460830178924398484922076248766509909499342148785790039585049283656451358975L,
                              5L: 90022260026940719086649458685820469676814156683365485772963019848106668196095L,
                              6L: 83737892266848770344209478015711919572202923197328142087712274118479341158401L,
                              7L: 34667965620820543567793729481600811750612646439558795709621156892698571440385L,
                              8L: 63456349992147796142899484244105564613077224608371012703923436064819027378433L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=1000000000000000000L, 
                                code='`\x18a\x01\x00\na\x01\x00\n`\x00U`\x18`\xff\na\x01\x00\n`'\
                                     '\x01U`\x18a\x01\x01\na\x01\x00\n`\x02U`\x18a\x01\x00\n`\xff'\
                                     '\n`\x03U`\x18`\xff\n`\xff\n`\x04U`\x18a\x01\x01\n`\xff'\
                                     '\n`\x05U`\x18a\x01\x00\na\x01\x01\n`\x06U`\x18`\xff\na'\
                                     '\x01\x01\n`\x07U`\x18a\x01\x01\na\x01\x01\n`\x08U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069521887415590932569929099639409724315265L
        price = 100000000000000L
        data = ''
        caller = 1170859069521887415590932569929099639409724315265L
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

    def test_arith1(self):
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
                             'balance': 1000000000000000000L,
                             'code': '`\x01`\x01\x90\x01`\x07\x02`\x05\x01`\x02\x90\x04`\x04\x90`\x01`!\x90\x05`\x15\x01`\x03\x02`\x05\x90\x07`\x03\x03`\t`\x11\n`\x00R`\x08`\x00\xf3',
                             'storage': {
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=1000000000000000000L, 
                                code='`\x01`\x01\x90\x01`\x07\x02`\x05\x01`\x02\x90\x04`\x04\x90`\x01`!'\
                                     '\x90\x05`\x15\x01`\x03\x02`\x05\x90\x07`\x03\x03`\t`\x11\n`\x00R'\
                                     '`\x08`\x00\xf3', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069521887415590932569929099639409724315265L
        price = 100000000000000L
        data = ''
        caller = 1170859069521887415590932569929099639409724315265L
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

    def test_addmod0(self):
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
                             'balance': 1000000000000000000L,
                             'code': '`\x02`\x02`\x01\x08`\x00U',
                             'storage': {
                              0L: 1L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=1000000000000000000L, 
                                code='`\x02`\x02`\x01\x08`\x00U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069521887415590932569929099639409724315265L
        price = 100000000000000L
        data = ''
        caller = 1170859069521887415590932569929099639409724315265L
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

    def test_addmod1(self):
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
                             'balance': 1000000000000000000L,
                             'code': '`\x02`\x02`\x00\x03`\x01`\x00\x03\x08`\x00U',
                             'storage': {
                              0L: 1L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=1000000000000000000L, 
                                code='`\x02`\x02`\x00\x03`\x01`\x00\x03\x08`\x00U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069521887415590932569929099639409724315265L
        price = 100000000000000L
        data = ''
        caller = 1170859069521887415590932569929099639409724315265L
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

    def test_expPowerOf256Of256_28(self):
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
                             'balance': 1000000000000000000L,
                             'code': '`\x1ca\x01\x00\na\x01\x00\n`\x00U`\x1c`\xff\na\x01\x00\n`\x01U`\x1ca\x01\x01\na\x01\x00\n`\x02U`\x1ca\x01\x00\n`\xff\n`\x03U`\x1c`\xff\n`\xff\n`\x04U`\x1ca\x01\x01\n`\xff\n`'\
                             '\x05U`\x1ca\x01\x00\na\x01\x01\n`\x06U`\x1c`\xff\na\x01\x01\n`\x07U`\x1ca\x01\x01\na\x01\x01\n`\x08U',
                             'storage': {
                              3L: 9497679494969858173111228280487696204805187236545917538996138972524253806593L,
                              4L: 115713305055813628029830397870082340621250109295361800782843501472376682709247L,
                              5L: 4299935168788447616930174254794111967803711819433703141028002505899609161983L,
                              6L: 48396598276623461154344680926355514803313977612377488861774531425231018393601L,
                              7L: 11701876412405919828967277792221997215490266144933920662620311123106761801985L,
                              8L: 16396339996675966641824655691596686069377228532714487479381181772823590076673L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=1000000000000000000L, 
                                code='`\x1ca\x01\x00\na\x01\x00\n`\x00U`\x1c`\xff\na\x01\x00\n`'\
                                     '\x01U`\x1ca\x01\x01\na\x01\x00\n`\x02U`\x1ca\x01\x00\n`\xff'\
                                     '\n`\x03U`\x1c`\xff\n`\xff\n`\x04U`\x1ca\x01\x01\n`\xff'\
                                     '\n`\x05U`\x1ca\x01\x00\na\x01\x01\n`\x06U`\x1c`\xff\na'\
                                     '\x01\x01\n`\x07U`\x1ca\x01\x01\na\x01\x01\n`\x08U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069521887415590932569929099639409724315265L
        price = 100000000000000L
        data = ''
        caller = 1170859069521887415590932569929099639409724315265L
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

    def test_expPowerOf256Of256_29(self):
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
                             'balance': 1000000000000000000L,
                             'code': '`\x1da\x01\x00\na\x01\x00\n`\x00U`\x1d`\xff\na\x01\x00\n`\x01U`\x1da\x01\x01\na\x01\x00\n`\x02U`\x1da\x01\x00\n`\xff\n`\x03U`\x1d`\xff\n`\xff\n`\x04U`\x1da\x01\x01\n`\xff\n`'\
                             '\x05U`\x1da\x01\x00\na\x01\x01\n`\x06U`\x1d`\xff\na\x01\x01\n`\x07U`\x1da\x01\x01\na\x01\x01\n`\x08U',
                             'storage': {
                              3L: 115564165965959783845054739631092071364728239242943609193859896807946381688833L,
                              4L: 29796811703898097440410573382566381985909385283921616312244836775545701924607L,
                              5L: 76104085449040805828347092808887448743067930323369183960769396019351951048959L,
                              6L: 115567699660089340613713906226093557201759894210737360431776140020348966928385L,
                              7L: 8209822676187988811602632091276622081528672854534573424947815086289865015041L,
                              8L: 41969510495593925548691353067322800651185377980400075429162359216161003733249L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=1000000000000000000L, 
                                code='`\x1da\x01\x00\na\x01\x00\n`\x00U`\x1d`\xff\na\x01\x00\n`'\
                                     '\x01U`\x1da\x01\x01\na\x01\x00\n`\x02U`\x1da\x01\x00\n`\xff'\
                                     '\n`\x03U`\x1d`\xff\n`\xff\n`\x04U`\x1da\x01\x01\n`\xff'\
                                     '\n`\x05U`\x1da\x01\x00\na\x01\x01\n`\x06U`\x1d`\xff\na'\
                                     '\x01\x01\n`\x07U`\x1da\x01\x01\na\x01\x01\n`\x08U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069521887415590932569929099639409724315265L
        price = 100000000000000L
        data = ''
        caller = 1170859069521887415590932569929099639409724315265L
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

    def test_divBoostBug(self):
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
                             'balance': 1000000000000000000L,
                             'code': '\x7f\x01\xda\xe6\x07k\x98\x1d\xae`v\xb9\x81\xda\xe6\x07k\x98\x1d\xae`v\xb9\x81\xda\xe6\x07k\x98\x1d\xae`w\x7f\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xba\x04`\x00U',
                             'storage': {
                              0L: 137L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=1000000000000000000L, 
                                code='\x7f\x01\xda\xe6\x07k\x98\x1d\xae`v\xb9\x81\xda\xe6\x07k\x98\x1d\xae`v\xb9'\
                                     '\x81\xda\xe6\x07k\x98\x1d\xae`w\x7f\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff'\
                                     '\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xba\x04`\x00'\
                                     'U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069521887415590932569929099639409724315265L
        price = 100000000000000L
        data = ''
        caller = 1170859069521887415590932569929099639409724315265L
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

    def test_divByNonZero2(self):
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
                             'balance': 1000000000000000000L,
                             'code': '`\x18`\x00\x04`\x00U',
                             'storage': {
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=1000000000000000000L, 
                                code='`\x18`\x00\x04`\x00U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069521887415590932569929099639409724315265L
        price = 100000000000000L
        data = ''
        caller = 1170859069521887415590932569929099639409724315265L
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

    def test_divByNonZero3(self):
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
                             'balance': 1000000000000000000L,
                             'code': '`\x01`\x01\x04`\x00U',
                             'storage': {
                              0L: 1L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=1000000000000000000L, 
                                code='`\x01`\x01\x04`\x00U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069521887415590932569929099639409724315265L
        price = 100000000000000L
        data = ''
        caller = 1170859069521887415590932569929099639409724315265L
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

    def test_divByNonZero0(self):
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
                             'balance': 1000000000000000000L,
                             'code': '`\x02`\x05\x04`\x00U',
                             'storage': {
                              0L: 2L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=1000000000000000000L, 
                                code='`\x02`\x05\x04`\x00U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069521887415590932569929099639409724315265L
        price = 100000000000000L
        data = ''
        caller = 1170859069521887415590932569929099639409724315265L
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

    def test_divByNonZero1(self):
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
                             'balance': 1000000000000000000L,
                             'code': '`\x18`\x17\x04`\x00U',
                             'storage': {
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=1000000000000000000L, 
                                code='`\x18`\x17\x04`\x00U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069521887415590932569929099639409724315265L
        price = 100000000000000L
        data = ''
        caller = 1170859069521887415590932569929099639409724315265L
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

    def test_signextend_AlmostBiggestByte(self):
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
                             'balance': 1000000000000000000L,
                             'code': '\x7f\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xfe\x7f\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xfe\x0b`\x00U',
                             'storage': {
                              0L: 115792089237316195423570985008687907853269984665640564039457584007913129639934L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=1000000000000000000L, 
                                code='\x7f\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff'\
                                     '\xff\xff\xff\xff\xff\xff\xff\xff\xff\xfe\x7f\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff'\
                                     '\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xfe\x0b`\x00'\
                                     'U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069521887415590932569929099639409724315265L
        price = 100000000000000L
        data = ''
        caller = 1170859069521887415590932569929099639409724315265L
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

    def test_modByZero(self):
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
                             'balance': 1000000000000000000L,
                             'code': '`\x01`\x00`\x03\x06\x03`\x00U',
                             'storage': {
                              0L: 115792089237316195423570985008687907853269984665640564039457584007913129639935L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=1000000000000000000L, 
                                code='`\x01`\x00`\x03\x06\x03`\x00U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069521887415590932569929099639409724315265L
        price = 100000000000000L
        data = ''
        caller = 1170859069521887415590932569929099639409724315265L
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

    def test_addmod1_overflow4(self):
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
                             'balance': 1000000000000000000L,
                             'code': '`\x05`\x02`\x01`\x00\x03\x08`\x00U',
                             'storage': {
                              0L: 2L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=1000000000000000000L, 
                                code='`\x05`\x02`\x01`\x00\x03\x08`\x00U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069521887415590932569929099639409724315265L
        price = 100000000000000L
        data = ''
        caller = 1170859069521887415590932569929099639409724315265L
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

    def test_signextendInvalidByteNumber(self):
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
                             'balance': 1000000000000000000L,
                             'code': 'b\x12j\xf4`P\x0b`\x00U',
                             'storage': {
                              0L: 1207028L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=1000000000000000000L, 
                                code='b\x12j\xf4`P\x0b`\x00U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069521887415590932569929099639409724315265L
        price = 100000000000000L
        data = ''
        caller = 1170859069521887415590932569929099639409724315265L
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

    def test_expPowerOf2_16(self):
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
                             'balance': 1000000000000000000L,
                             'code': '`\x10`\x02\n`\x00U`\x0f`\x02\n`\x01U`\x11`\x02\n`\x02U',
                             'storage': {
                              0L: 65536L,
                              1L: 32768L,
                              2L: 131072L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=1000000000000000000L, 
                                code='`\x10`\x02\n`\x00U`\x0f`\x02\n`\x01U`\x11`\x02\n`\x02'\
                                     'U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069521887415590932569929099639409724315265L
        price = 100000000000000L
        data = ''
        caller = 1170859069521887415590932569929099639409724315265L
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

    def test_divByZero_2(self):
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
                             'balance': 1000000000000000000L,
                             'code': '`\x07`\x00`\r\x04\x01`\x00U',
                             'storage': {
                              0L: 7L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=1000000000000000000L, 
                                code='`\x07`\x00`\r\x04\x01`\x00U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069521887415590932569929099639409724315265L
        price = 100000000000000L
        data = ''
        caller = 1170859069521887415590932569929099639409724315265L
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

    def test_signextend_BigByte_0(self):
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
                             'balance': 1000000000000000000L,
                             'code': '`\x00\x7f\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\x0b`\x00U',
                             'storage': {
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=1000000000000000000L, 
                                code='`\x00\x7f\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff'\
                                     '\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\x0b`\x00U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069521887415590932569929099639409724315265L
        price = 100000000000000L
        data = ''
        caller = 1170859069521887415590932569929099639409724315265L
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

    def test_sub4(self):
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
                             'balance': 1000000000000000000L,
                             'code': '`\x00\x7f\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\x03`\x00U',
                             'storage': {
                              0L: 115792089237316195423570985008687907853269984665640564039457584007913129639935L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=1000000000000000000L, 
                                code='`\x00\x7f\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff'\
                                     '\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\x03`\x00U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069521887415590932569929099639409724315265L
        price = 100000000000000L
        data = ''
        caller = 1170859069521887415590932569929099639409724315265L
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

    def test_expPowerOf256Of256_27(self):
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
                             'balance': 1000000000000000000L,
                             'code': '`\x1ba\x01\x00\na\x01\x00\n`\x00U`\x1b`\xff\na\x01\x00\n`\x01U`\x1ba\x01\x01\na\x01\x00\n`\x02U`\x1ba\x01\x00\n`\xff\n`\x03U`\x1b`\xff\n`\xff\n`\x04U`\x1ba\x01\x01\n`\xff\n`'\
                             '\x05U`\x1ba\x01\x00\na\x01\x01\n`\x06U`\x1b`\xff\na\x01\x01\n`\x07U`\x1ba\x01\x01\na\x01\x01\n`\x08U',
                             'storage': {
                              3L: 38483692440104869020221269351636561967706069858656226019112854607988829192193L,
                              4L: 10645426101861250165015700741141466012883289588076566266701569922896236248831L,
                              5L: 25748258427330701187106324113792620342456959469328998556434781418740772438271L,
                              6L: 77082233471173346418599266142200390038512544417075286623318608643634621317121L,
                              7L: 94151869200341398878616437045666795696078883504233219193427246506933705506561L,
                              8L: 12350951291019601932674792934478196555907435661086930635755345915574960718081L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=1000000000000000000L, 
                                code='`\x1ba\x01\x00\na\x01\x00\n`\x00U`\x1b`\xff\na\x01\x00\n`'\
                                     '\x01U`\x1ba\x01\x01\na\x01\x00\n`\x02U`\x1ba\x01\x00\n`\xff'\
                                     '\n`\x03U`\x1b`\xff\n`\xff\n`\x04U`\x1ba\x01\x01\n`\xff'\
                                     '\n`\x05U`\x1ba\x01\x00\na\x01\x01\n`\x06U`\x1b`\xff\na'\
                                     '\x01\x01\n`\x07U`\x1ba\x01\x01\na\x01\x01\n`\x08U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069521887415590932569929099639409724315265L
        price = 100000000000000L
        data = ''
        caller = 1170859069521887415590932569929099639409724315265L
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

    def test_signextend_BigBytePlus1_2(self):
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
                             'balance': 1000000000000000000L,
                             'code': '`\xffh\xf0\x00\x00\x00\x00\x00\x00\x00\x01\x0b`\x00U',
                             'storage': {
                              0L: 255L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=1000000000000000000L, 
                                code='`\xffh\xf0\x00\x00\x00\x00\x00\x00\x00\x01\x0b`\x00U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069521887415590932569929099639409724315265L
        price = 100000000000000L
        data = ''
        caller = 1170859069521887415590932569929099639409724315265L
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

    def test_sub2(self):
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
                             'balance': 1000000000000000000L,
                             'code': '`\x17`\x00\x03`\x00U',
                             'storage': {
                              0L: 115792089237316195423570985008687907853269984665640564039457584007913129639913L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=1000000000000000000L, 
                                code='`\x17`\x00\x03`\x00U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069521887415590932569929099639409724315265L
        price = 100000000000000L
        data = ''
        caller = 1170859069521887415590932569929099639409724315265L
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

    def test_addmod2_1(self):
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
                             'balance': 1000000000000000000L,
                             'code': '`\x03`\x01`\x06`\x00\x03\x08`\x03`\x05`\x00\x03\x06\x14`\x00U',
                             'storage': {
                              0L: 1L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=1000000000000000000L, 
                                code='`\x03`\x01`\x06`\x00\x03\x08`\x03`\x05`\x00\x03\x06\x14`\x00U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069521887415590932569929099639409724315265L
        price = 100000000000000L
        data = ''
        caller = 1170859069521887415590932569929099639409724315265L
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

    def test_addmod2_0(self):
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
                             'balance': 1000000000000000000L,
                             'code': '`\x03`\x01`\x06`\x00\x03\x08`\x03`\x05`\x00\x03\x07\x14`\x00U',
                             'storage': {
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=1000000000000000000L, 
                                code='`\x03`\x01`\x06`\x00\x03\x08`\x03`\x05`\x00\x03\x07\x14`\x00U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069521887415590932569929099639409724315265L
        price = 100000000000000L
        data = ''
        caller = 1170859069521887415590932569929099639409724315265L
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

    def test_smod_i256min1(self):
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
                             'balance': 1000000000000000000L,
                             'code': '`\x01`\x00\x03\x7f\x80\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00`\x00\x03\x07`\x00U',
                             'storage': {
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=1000000000000000000L, 
                                code='`\x01`\x00\x03\x7f\x80\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00'\
                                     '\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00`\x00\x03\x07`\x00U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069521887415590932569929099639409724315265L
        price = 100000000000000L
        data = ''
        caller = 1170859069521887415590932569929099639409724315265L
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

    def test_mulmod3_0(self):
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
                             'balance': 1000000000000000000L,
                             'code': '`\x02`\x03`\x00\x03`\x01`\x05\t\x14`\x00U',
                             'storage': {
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=1000000000000000000L, 
                                code='`\x02`\x03`\x00\x03`\x01`\x05\t\x14`\x00U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069521887415590932569929099639409724315265L
        price = 100000000000000L
        data = ''
        caller = 1170859069521887415590932569929099639409724315265L
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

    def test_div1(self):
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
                             'balance': 1000000000000000000L,
                             'code': '`\x02\x7f\xfe\xdc\xba\x98vT2\x10\xfe\xdc\xba\x98vT2\x10\xfe\xdc\xba\x98vT2\x10\xfe\xdc\xba\x98vT2\x10\x04`\x00R` `\x00\xf3',
                             'storage': {
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=1000000000000000000L, 
                                code='`\x02\x7f\xfe\xdc\xba\x98vT2\x10\xfe\xdc\xba\x98vT2\x10\xfe\xdc\xba\x98'\
                                     'vT2\x10\xfe\xdc\xba\x98vT2\x10\x04`\x00R` `\x00\xf3', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069521887415590932569929099639409724315265L
        price = 100000000000000L
        data = ''
        caller = 1170859069521887415590932569929099639409724315265L
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

    def test_smod7(self):
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
                             'balance': 1000000000000000000L,
                             'code': '\x7f\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\x7f\x7f\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff`\x00\x03\x07`'\
                             '\x00U',
                             'storage': {
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=1000000000000000000L, 
                                code='\x7f\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff'\
                                     '\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\x7f\x7f\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff'\
                                     '\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff`\x00\x03'\
                                     '\x07`\x00U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069521887415590932569929099639409724315265L
        price = 100000000000000L
        data = ''
        caller = 1170859069521887415590932569929099639409724315265L
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

    def test_sdiv_i256min(self):
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
                             'balance': 1000000000000000000L,
                             'code': '`\x01`\x00\x03\x7f\x7f\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff`\x00\x03\x05`\x00U',
                             'storage': {
                              0L: 57896044618658097711785492504343953926634992332820282019728792003956564819967L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=1000000000000000000L, 
                                code='`\x01`\x00\x03\x7f\x7f\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff'\
                                     '\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff`\x00\x03\x05`\x00U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069521887415590932569929099639409724315265L
        price = 100000000000000L
        data = ''
        caller = 1170859069521887415590932569929099639409724315265L
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

    def test_expPowerOf2_4(self):
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
                             'balance': 1000000000000000000L,
                             'code': '`\x04`\x02\n`\x00U`\x03`\x02\n`\x01U`\x05`\x02\n`\x02U',
                             'storage': {
                              0L: 16L,
                              1L: 8L,
                              2L: 32L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=1000000000000000000L, 
                                code='`\x04`\x02\n`\x00U`\x03`\x02\n`\x01U`\x05`\x02\n`\x02'\
                                     'U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069521887415590932569929099639409724315265L
        price = 100000000000000L
        data = ''
        caller = 1170859069521887415590932569929099639409724315265L
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

    def test_sub0(self):
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
                             'balance': 1000000000000000000L,
                             'code': '`\x01`\x17\x03`\x00U',
                             'storage': {
                              0L: 22L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=1000000000000000000L, 
                                code='`\x01`\x17\x03`\x00U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069521887415590932569929099639409724315265L
        price = 100000000000000L
        data = ''
        caller = 1170859069521887415590932569929099639409724315265L
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

    def test_mul6(self):
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
                             'balance': 1000000000000000000L,
                             'code': '\x7f\x7f\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\x7f\x7f\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\x02`\x00U',
                             'storage': {
                              0L: 1L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=1000000000000000000L, 
                                code='\x7f\x7f\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff'\
                                     '\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\x7f\x7f\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff'\
                                     '\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\x02`\x00'\
                                     'U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069521887415590932569929099639409724315265L
        price = 100000000000000L
        data = ''
        caller = 1170859069521887415590932569929099639409724315265L
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

    def test_sub1(self):
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
                             'balance': 1000000000000000000L,
                             'code': '`\x03`\x02\x03`\x00U',
                             'storage': {
                              0L: 115792089237316195423570985008687907853269984665640564039457584007913129639935L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=1000000000000000000L, 
                                code='`\x03`\x02\x03`\x00U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069521887415590932569929099639409724315265L
        price = 100000000000000L
        data = ''
        caller = 1170859069521887415590932569929099639409724315265L
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

    def test_mul7(self):
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
                             'balance': 1000000000000000000L,
                             'code': 'p\x01#Eg\x89\n\xbc\xde\xf0\xfe\xdc\xba\t\x87eC!p\x01#Eg\x89\n\xbc\xde\xf0\xfe\xdc\xba\t\x87eC!p\x01#Eg\x89\n\xbc\xde\xf0\xfe\xdc\xba\t\x87eC!\x02\x02`\x00R` `\x00\xf3',
                             'storage': {
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=1000000000000000000L, 
                                code='p\x01#Eg\x89\n\xbc\xde\xf0\xfe\xdc\xba\t\x87eC!p\x01#Eg'\
                                     '\x89\n\xbc\xde\xf0\xfe\xdc\xba\t\x87eC!p\x01#Eg\x89\n\xbc\xde\xf0'\
                                     '\xfe\xdc\xba\t\x87eC!\x02\x02`\x00R` `\x00\xf3', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069521887415590932569929099639409724315265L
        price = 100000000000000L
        data = ''
        caller = 1170859069521887415590932569929099639409724315265L
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

    def test_expPowerOf2_256(self):
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
                             'balance': 1000000000000000000L,
                             'code': 'a\x01\x00`\x02\n`\x00U`\xff`\x02\n`\x01Ua\x01\x01`\x02\n`\x02U',
                             'storage': {
                              1L: 57896044618658097711785492504343953926634992332820282019728792003956564819968L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=1000000000000000000L, 
                                code='a\x01\x00`\x02\n`\x00U`\xff`\x02\n`\x01Ua\x01\x01`\x02\n'\
                                     '`\x02U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069521887415590932569929099639409724315265L
        price = 100000000000000L
        data = ''
        caller = 1170859069521887415590932569929099639409724315265L
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

    def test_mulmod1_overflow(self):
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
                             'balance': 1000000000000000000L,
                             'code': '`\x05`\x02`\x01`\x00\x03\t`\x00U',
                             'storage': {
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=1000000000000000000L, 
                                code='`\x05`\x02`\x01`\x00\x03\t`\x00U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069521887415590932569929099639409724315265L
        price = 100000000000000L
        data = ''
        caller = 1170859069521887415590932569929099639409724315265L
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

    def test_addmod2(self):
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
                             'balance': 1000000000000000000L,
                             'code': '`\x03`\x01`\x06`\x00\x03\x08`\x00U',
                             'storage': {
                              0L: 2L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=1000000000000000000L, 
                                code='`\x03`\x01`\x06`\x00\x03\x08`\x00U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069521887415590932569929099639409724315265L
        price = 100000000000000L
        data = ''
        caller = 1170859069521887415590932569929099639409724315265L
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

    def test_smod_i256min2(self):
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
                             'balance': 1000000000000000000L,
                             'code': '`\x01`\x01`\x00\x03\x7f\x80\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00`\x00\x03\x07\x03`\x00U',
                             'storage': {
                              0L: 115792089237316195423570985008687907853269984665640564039457584007913129639935L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=1000000000000000000L, 
                                code='`\x01`\x01`\x00\x03\x7f\x80\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00'\
                                     '\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00`\x00\x03\x07\x03`'\
                                     '\x00U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069521887415590932569929099639409724315265L
        price = 100000000000000L
        data = ''
        caller = 1170859069521887415590932569929099639409724315265L
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

    def test_expPowerOf256Of256_1(self):
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
                             'balance': 1000000000000000000L,
                             'code': '`\x01a\x01\x00\na\x01\x00\n`\x00U`\x01`\xff\na\x01\x00\n`\x01U`\x01a\x01\x01\na\x01\x00\n`\x02U`\x01a\x01\x00\n`\xff\n`\x03U`\x01`\xff\n`\xff\n`\x04U`\x01a\x01\x01\n`\xff\n`'\
                             '\x05U`\x01a\x01\x00\na\x01\x01\n`\x06U`\x01`\xff\na\x01\x01\n`\x07U`\x01a\x01\x01\na\x01\x01\n`\x08U',
                             'storage': {
                              3L: 3059605063183016712277721510764259762596496903723495948835695681317069848577L,
                              4L: 64946385749017250832482072853933863069726291388589506484671647877697625915135L,
                              5L: 85446755687772089089393075192758792342486802455648082716356894688374033547519L,
                              6L: 1226038936089917454166061297023693466909118688613925930124971309282338340865L,
                              7L: 90115345861475988335285459389239709198914031330026174061562808454832327884545L,
                              8L: 83507828100476394873535783317713405289103533642497835963202458469734694322433L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=1000000000000000000L, 
                                code='`\x01a\x01\x00\na\x01\x00\n`\x00U`\x01`\xff\na\x01\x00\n`'\
                                     '\x01U`\x01a\x01\x01\na\x01\x00\n`\x02U`\x01a\x01\x00\n`\xff'\
                                     '\n`\x03U`\x01`\xff\n`\xff\n`\x04U`\x01a\x01\x01\n`\xff'\
                                     '\n`\x05U`\x01a\x01\x00\na\x01\x01\n`\x06U`\x01`\xff\na'\
                                     '\x01\x01\n`\x07U`\x01a\x01\x01\na\x01\x01\n`\x08U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069521887415590932569929099639409724315265L
        price = 100000000000000L
        data = ''
        caller = 1170859069521887415590932569929099639409724315265L
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

    def test_expPowerOf256Of256_0(self):
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
                             'balance': 1000000000000000000L,
                             'code': '`\x00a\x01\x00\na\x01\x00\n`\x00U`\x00`\xff\na\x01\x00\n`\x01U`\x00a\x01\x01\na\x01\x00\n`\x02U`\x00a\x01\x00\n`\xff\n`\x03U`\x00`\xff\n`\xff\n`\x04U`\x00a\x01\x01\n`\xff\n`'\
                             '\x05U`\x00a\x01\x00\na\x01\x01\n`\x06U`\x00`\xff\na\x01\x01\n`\x07U`\x00a\x01\x01\na\x01\x01\n`\x08U',
                             'storage': {
                              0L: 256L,
                              1L: 256L,
                              2L: 256L,
                              3L: 255L,
                              4L: 255L,
                              5L: 255L,
                              6L: 257L,
                              7L: 257L,
                              8L: 257L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=1000000000000000000L, 
                                code='`\x00a\x01\x00\na\x01\x00\n`\x00U`\x00`\xff\na\x01\x00\n`'\
                                     '\x01U`\x00a\x01\x01\na\x01\x00\n`\x02U`\x00a\x01\x00\n`\xff'\
                                     '\n`\x03U`\x00`\xff\n`\xff\n`\x04U`\x00a\x01\x01\n`\xff'\
                                     '\n`\x05U`\x00a\x01\x00\na\x01\x01\n`\x06U`\x00`\xff\na'\
                                     '\x01\x01\n`\x07U`\x00a\x01\x01\na\x01\x01\n`\x08U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069521887415590932569929099639409724315265L
        price = 100000000000000L
        data = ''
        caller = 1170859069521887415590932569929099639409724315265L
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

    def test_expPowerOf256Of256_3(self):
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
                             'balance': 1000000000000000000L,
                             'code': '`\x03a\x01\x00\na\x01\x00\n`\x00U`\x03`\xff\na\x01\x00\n`\x01U`\x03a\x01\x01\na\x01\x00\n`\x02U`\x03a\x01\x00\n`\xff\n`\x03U`\x03`\xff\n`\xff\n`\x04U`\x03a\x01\x01\n`\xff\n`'\
                             '\x05U`\x03a\x01\x00\na\x01\x01\n`\x06U`\x03`\xff\na\x01\x01\n`\x07U`\x03a\x01\x01\na\x01\x01\n`\x08U',
                             'storage': {
                              3L: 7509106097093730011630093237202784650072841651671912529772991585339238776833L,
                              4L: 38290356903089152037544434592592465510243346109437057546044682301961169665791L,
                              5L: 42129814684646543126348356257504972372034277499141030862086683680913974558975L,
                              6L: 18796044789528149052406582351866041199292954077820157477205660679666629869569L,
                              7L: 30399330551861971515974303894253779338600539720187268158424855738354206244609L,
                              8L: 108980024387197914276205543464773254377859711155926716677281663773064325955841L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=1000000000000000000L, 
                                code='`\x03a\x01\x00\na\x01\x00\n`\x00U`\x03`\xff\na\x01\x00\n`'\
                                     '\x01U`\x03a\x01\x01\na\x01\x00\n`\x02U`\x03a\x01\x00\n`\xff'\
                                     '\n`\x03U`\x03`\xff\n`\xff\n`\x04U`\x03a\x01\x01\n`\xff'\
                                     '\n`\x05U`\x03a\x01\x00\na\x01\x01\n`\x06U`\x03`\xff\na'\
                                     '\x01\x01\n`\x07U`\x03a\x01\x01\na\x01\x01\n`\x08U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069521887415590932569929099639409724315265L
        price = 100000000000000L
        data = ''
        caller = 1170859069521887415590932569929099639409724315265L
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

    def test_expPowerOf256Of256_2(self):
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
                             'balance': 1000000000000000000L,
                             'code': '`\x02a\x01\x00\na\x01\x00\n`\x00U`\x02`\xff\na\x01\x00\n`\x01U`\x02a\x01\x01\na\x01\x00\n`\x02U`\x02a\x01\x00\n`\xff\n`\x03U`\x02`\xff\n`\xff\n`\x04U`\x02a\x01\x01\n`\xff\n`'\
                             '\x05U`\x02a\x01\x00\na\x01\x01\n`\x06U`\x02`\xff\na\x01\x01\n`\x07U`\x02a\x01\x01\na\x01\x01\n`\x08U',
                             'storage': {
                              3L: 35684671406788450058690691174653691892701243064536139020904391158652521676801L,
                              4L: 59232513320897970918910043598136467678606867980584390145697722881629753311487L,
                              5L: 58705239428236352267206187056125671899556905316536924076733713273217202913535L,
                              6L: 46324544842152038903000162237961413134741269428713822661041693336878771601409L,
                              7L: 106379458411604270640200723872979572934101195248236840362867346110552152604929L,
                              8L: 51932325499082483871443854601774097918978859083286306620359033691760211656961L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=1000000000000000000L, 
                                code='`\x02a\x01\x00\na\x01\x00\n`\x00U`\x02`\xff\na\x01\x00\n`'\
                                     '\x01U`\x02a\x01\x01\na\x01\x00\n`\x02U`\x02a\x01\x00\n`\xff'\
                                     '\n`\x03U`\x02`\xff\n`\xff\n`\x04U`\x02a\x01\x01\n`\xff'\
                                     '\n`\x05U`\x02a\x01\x00\na\x01\x01\n`\x06U`\x02`\xff\na'\
                                     '\x01\x01\n`\x07U`\x02a\x01\x01\na\x01\x01\n`\x08U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069521887415590932569929099639409724315265L
        price = 100000000000000L
        data = ''
        caller = 1170859069521887415590932569929099639409724315265L
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

    def test_expPowerOf256Of256_5(self):
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
                             'balance': 1000000000000000000L,
                             'code': '`\x05a\x01\x00\na\x01\x00\n`\x00U`\x05`\xff\na\x01\x00\n`\x01U`\x05a\x01\x01\na\x01\x00\n`\x02U`\x05a\x01\x00\n`\xff\n`\x03U`\x05`\xff\n`\xff\n`\x04U`\x05a\x01\x01\n`\xff\n`'\
                             '\x05U`\x05a\x01\x00\na\x01\x01\n`\x06U`\x05`\xff\na\x01\x01\n`\x07U`\x05a\x01\x01\na\x01\x01\n`\x08U',
                             'storage': {
                              3L: 82097736621887453144738928706488282125439196973497094669655819961703340179457L,
                              4L: 53133720224321890553799294263499314496700729388928679458153706176025830096639L,
                              5L: 114096355291310632328912361731577724574561909388773748730554036700263630569727L,
                              6L: 93526145388008191859340524611820427621352466814415752457515217250352065675265L,
                              7L: 50961515925585147602326301824865680942396506779474973511120656365903759671041L,
                              8L: 82381723258049923464777114727664785506799309587382046227484519819802942177537L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=1000000000000000000L, 
                                code='`\x05a\x01\x00\na\x01\x00\n`\x00U`\x05`\xff\na\x01\x00\n`'\
                                     '\x01U`\x05a\x01\x01\na\x01\x00\n`\x02U`\x05a\x01\x00\n`\xff'\
                                     '\n`\x03U`\x05`\xff\n`\xff\n`\x04U`\x05a\x01\x01\n`\xff'\
                                     '\n`\x05U`\x05a\x01\x00\na\x01\x01\n`\x06U`\x05`\xff\na'\
                                     '\x01\x01\n`\x07U`\x05a\x01\x01\na\x01\x01\n`\x08U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069521887415590932569929099639409724315265L
        price = 100000000000000L
        data = ''
        caller = 1170859069521887415590932569929099639409724315265L
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

    def test_expPowerOf256Of256_4(self):
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
                             'balance': 1000000000000000000L,
                             'code': '`\x04a\x01\x00\na\x01\x00\n`\x00U`\x04`\xff\na\x01\x00\n`\x01U`\x04a\x01\x01\na\x01\x00\n`\x02U`\x04a\x01\x00\n`\xff\n`\x03U`\x04`\xff\n`\xff\n`\x04U`\x04a\x01\x01\n`\xff\n`'\
                             '\x05U`\x04a\x01\x00\na\x01\x01\n`\x06U`\x04`\xff\na\x01\x01\n`\x07U`\x04a\x01\x01\na\x01\x01\n`\x08U',
                             'storage': {
                              3L: 104180459307073179463913335729947524956342847659456996136147549665912581783553L,
                              4L: 45751977055995076893837051142492326735442329149693349358278717162318234124543L,
                              5L: 105546705083962239776280838125382873088043929909358687231796858176367034106111L,
                              6L: 104614202261512011900638534567018544938205717373709248053501147660488462565377L,
                              7L: 20805755454287356068906442693618939408693780123187819689785872758108948529409L,
                              8L: 101965897610888126403407041783167308378486948961680044692678870984371172802817L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=1000000000000000000L, 
                                code='`\x04a\x01\x00\na\x01\x00\n`\x00U`\x04`\xff\na\x01\x00\n`'\
                                     '\x01U`\x04a\x01\x01\na\x01\x00\n`\x02U`\x04a\x01\x00\n`\xff'\
                                     '\n`\x03U`\x04`\xff\n`\xff\n`\x04U`\x04a\x01\x01\n`\xff'\
                                     '\n`\x05U`\x04a\x01\x00\na\x01\x01\n`\x06U`\x04`\xff\na'\
                                     '\x01\x01\n`\x07U`\x04a\x01\x01\na\x01\x01\n`\x08U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069521887415590932569929099639409724315265L
        price = 100000000000000L
        data = ''
        caller = 1170859069521887415590932569929099639409724315265L
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

    def test_expPowerOf2_64(self):
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
                             'balance': 1000000000000000000L,
                             'code': '`@`\x02\n`\x00U`?`\x02\n`\x01U`A`\x02\n`\x02U',
                             'storage': {
                              0L: 18446744073709551616L,
                              1L: 9223372036854775808L,
                              2L: 36893488147419103232L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=1000000000000000000L, 
                                code='`@`\x02\n`\x00U`?`\x02\n`\x01U`A`\x02\n`\x02'\
                                     'U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069521887415590932569929099639409724315265L
        price = 100000000000000L
        data = ''
        caller = 1170859069521887415590932569929099639409724315265L
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

    def test_expPowerOf256Of256_6(self):
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
                             'balance': 1000000000000000000L,
                             'code': '`\x06a\x01\x00\na\x01\x00\n`\x00U`\x06`\xff\na\x01\x00\n`\x01U`\x06a\x01\x01\na\x01\x00\n`\x02U`\x06a\x01\x00\n`\xff\n`\x03U`\x06`\xff\n`\xff\n`\x04U`\x06a\x01\x01\n`\xff\n`'\
                             '\x05U`\x06a\x01\x00\na\x01\x01\n`\x06U`\x06`\xff\na\x01\x01\n`\x07U`\x06a\x01\x01\na\x01\x01\n`\x08U',
                             'storage': {
                              3L: 11435072968476041248577174136455222083821632859290360317387830027612682452993L,
                              4L: 29838683424993676685700745244695845239470248567130516709948292817813784625407L,
                              5L: 107606274993353017652986210904939816968102791635211673659007043946902783918335L,
                              6L: 3725531100599457640655441464738752256474927916455295396851587668754273665025L,
                              7L: 39450714102859599482682422335408269864750442602220136464558252613040321724673L,
                              8L: 58367409542318765371006823048891477968631145636400631624472570914463275155713L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=1000000000000000000L, 
                                code='`\x06a\x01\x00\na\x01\x00\n`\x00U`\x06`\xff\na\x01\x00\n`'\
                                     '\x01U`\x06a\x01\x01\na\x01\x00\n`\x02U`\x06a\x01\x00\n`\xff'\
                                     '\n`\x03U`\x06`\xff\n`\xff\n`\x04U`\x06a\x01\x01\n`\xff'\
                                     '\n`\x05U`\x06a\x01\x00\na\x01\x01\n`\x06U`\x06`\xff\na'\
                                     '\x01\x01\n`\x07U`\x06a\x01\x01\na\x01\x01\n`\x08U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069521887415590932569929099639409724315265L
        price = 100000000000000L
        data = ''
        caller = 1170859069521887415590932569929099639409724315265L
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

    def test_expPowerOf256Of256_9(self):
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
                             'balance': 1000000000000000000L,
                             'code': '`\ta\x01\x00\na\x01\x00\n`\x00U`\t`\xff\na\x01\x00\n`\x01U`\ta\x01\x01\na\x01\x00\n`\x02U`\ta\x01\x00\n`\xff\n`\x03U`\t`\xff\n`\xff\n`\x04U`\ta\x01\x01\n`\xff\n`'\
                             '\x05U`\ta\x01\x00\na\x01\x01\n`\x06U`\t`\xff\na\x01\x01\n`\x07U`\ta\x01\x01\na\x01\x01\n`\x08U',
                             'storage': {
                              3L: 37544599844834186309489558325272750245245031648093458553266128448984962826241L,
                              4L: 32902293083653969256382290890943213921228732500552563030700054273598132059903L,
                              5L: 20900127223701187507569604367284576078235625433031513598122327338511564865791L,
                              6L: 556072892769477086587558712025699215307595196328648543389280473869891665921L,
                              7L: 110152184046086891254004814608804722935320045522148244199157782070981523275521L,
                              8L: 37242642928182852816882152052488410953256925480179486681539560659802290454785L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=1000000000000000000L, 
                                code='`\ta\x01\x00\na\x01\x00\n`\x00U`\t`\xff\na\x01\x00\n`'\
                                     '\x01U`\ta\x01\x01\na\x01\x00\n`\x02U`\ta\x01\x00\n`\xff'\
                                     '\n`\x03U`\t`\xff\n`\xff\n`\x04U`\ta\x01\x01\n`\xff'\
                                     '\n`\x05U`\ta\x01\x00\na\x01\x01\n`\x06U`\t`\xff\na'\
                                     '\x01\x01\n`\x07U`\ta\x01\x01\na\x01\x01\n`\x08U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069521887415590932569929099639409724315265L
        price = 100000000000000L
        data = ''
        caller = 1170859069521887415590932569929099639409724315265L
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

    def test_expXY(self):
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
                             'balance': 1000000000000000000L,
                             'code': '`\x005`\x00U` 5`\x01U`\x01T`\x00T\n`\x02U',
                             'storage': {
                              0L: 2L,
                              1L: 281474976710671L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=1000000000000000000L, 
                                code='`\x005`\x00U` 5`\x01U`\x01T`\x00T\n`\x02U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069521887415590932569929099639409724315265L
        price = 100000000000000L
        data = '\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x02\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x01\x00\x00\x00\x00\x00\x0f'
        caller = 1170859069521887415590932569929099639409724315265L
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

    def test_signextend_BitIsSetInHigherByte(self):
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
                             'balance': 1000000000000000000L,
                             'code': 'b\x12\xfa\xf4`\x01\x0b`\x00U',
                             'storage': {
                              0L: 115792089237316195423570985008687907853269984665640564039457584007913129638644L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=1000000000000000000L, 
                                code='b\x12\xfa\xf4`\x01\x0b`\x00U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069521887415590932569929099639409724315265L
        price = 100000000000000L
        data = ''
        caller = 1170859069521887415590932569929099639409724315265L
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

    def test_addmod3(self):
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
                             'balance': 1000000000000000000L,
                             'code': '`\x03`\x00\x03`\x01`\x04\x08`\x00U',
                             'storage': {
                              0L: 5L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=1000000000000000000L, 
                                code='`\x03`\x00\x03`\x01`\x04\x08`\x00U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069521887415590932569929099639409724315265L
        price = 100000000000000L
        data = ''
        caller = 1170859069521887415590932569929099639409724315265L
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

    def test_expPowerOf2_2(self):
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
                             'balance': 1000000000000000000L,
                             'code': '`\x02`\x02\n`\x00U`\x01`\x02\n`\x01U`\x03`\x02\n`\x02U',
                             'storage': {
                              0L: 4L,
                              1L: 2L,
                              2L: 8L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=1000000000000000000L, 
                                code='`\x02`\x02\n`\x00U`\x01`\x02\n`\x01U`\x03`\x02\n`\x02'\
                                     'U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069521887415590932569929099639409724315265L
        price = 100000000000000L
        data = ''
        caller = 1170859069521887415590932569929099639409724315265L
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

    def test_not1(self):
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
                             'balance': 1000000000000000000L,
                             'code': 'b\x01\xe2@`\x00R`\x00Q\x19`\x00R` `\x00\xf3',
                             'storage': {
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=1000000000000000000L, 
                                code='b\x01\xe2@`\x00R`\x00Q\x19`\x00R` `\x00\xf3', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069521887415590932569929099639409724315265L
        price = 100000000000000L
        data = ''
        caller = 1170859069521887415590932569929099639409724315265L
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

    def test_expPowerOf256_30(self):
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
                             'balance': 1000000000000000000L,
                             'code': '`\x1ea\x01\x00\n`\x00U`\x1e`\xff\n`\x01U`\x1ea\x01\x01\n`\x02U',
                             'storage': {
                              0L: 1766847064778384329583297500742918515827483896875618958121606201292619776L,
                              1L: 1571105731713312715511913444948824285516982702388429082930088043212890625L,
                              2L: 1986066106425567145468762597517802839695718885598475553669534044740853249L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=1000000000000000000L, 
                                code='`\x1ea\x01\x00\n`\x00U`\x1e`\xff\n`\x01U`\x1ea\x01\x01\n'\
                                     '`\x02U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069521887415590932569929099639409724315265L
        price = 100000000000000L
        data = ''
        caller = 1170859069521887415590932569929099639409724315265L
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

    def test_expPowerOf256_31(self):
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
                             'balance': 1000000000000000000L,
                             'code': '`\x1fa\x01\x00\n`\x00U`\x1f`\xff\n`\x01U`\x1fa\x01\x01\n`\x02U',
                             'storage': {
                              0L: 452312848583266388373324160190187140051835877600158453279131187530910662656L,
                              1L: 400631961586894742455537928461950192806830589109049416147172451019287109375L,
                              2L: 510418989351370756385471987562075329801799753598808217293070249498399284993L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=1000000000000000000L, 
                                code='`\x1fa\x01\x00\n`\x00U`\x1f`\xff\n`\x01U`\x1fa\x01\x01\n'\
                                     '`\x02U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069521887415590932569929099639409724315265L
        price = 100000000000000L
        data = ''
        caller = 1170859069521887415590932569929099639409724315265L
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

    def test_expPowerOf256_32(self):
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
                             'balance': 1000000000000000000L,
                             'code': '` a\x01\x00\n`\x00U` `\xff\n`\x01U` a\x01\x01\n`\x02U',
                             'storage': {
                              1L: 102161150204658159326162171757797299165741800222807601117528975009918212890625L,
                              2L: 15385591025986088967495315794765451905792552009253147804861470113175486603265L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=1000000000000000000L, 
                                code='` a\x01\x00\n`\x00U` `\xff\n`\x01U` a\x01\x01\n'\
                                     '`\x02U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069521887415590932569929099639409724315265L
        price = 100000000000000L
        data = ''
        caller = 1170859069521887415590932569929099639409724315265L
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

    def test_expPowerOf256_33(self):
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
                             'balance': 1000000000000000000L,
                             'code': '`!a\x01\x00\n`\x00U`!`\xff\n`\x01U`!a\x01\x01\n`\x02U',
                             'storage': {
                              1L: 113665313029002853291453156292219928131682491712451940131389809756603247763711L,
                              2L: 17165859609674220244882668959332272777506387746279808507839962817053649281281L
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=1000000000000000000L, 
                                code='`!a\x01\x00\n`\x00U`!`\xff\n`\x01U`!a\x01\x01\n'\
                                     '`\x02U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069521887415590932569929099639409724315265L
        price = 100000000000000L
        data = ''
        caller = 1170859069521887415590932569929099639409724315265L
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

    def test_mulmoddivByZero(self):
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
                             'balance': 1000000000000000000L,
                             'code': '`\x00`\x01`\x05\t`\x00U',
                             'storage': {
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=1000000000000000000L, 
                                code='`\x00`\x01`\x05\t`\x00U', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069521887415590932569929099639409724315265L
        price = 100000000000000L
        data = ''
        caller = 1170859069521887415590932569929099639409724315265L
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
