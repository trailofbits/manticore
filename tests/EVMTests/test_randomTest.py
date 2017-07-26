
import struct
import unittest
import json
from manticore.platforms import evm
from manticore.core import state
from manticore.core.smtlib import Operators, ConstraintSet
import os


class EVMTest_randomTest(unittest.TestCase):
    _multiprocess_can_split_ = True
    maxDiff=None 

    def test_randomVMtest(self):
        header ={
                   'hash': 42575053018967912481081396422302317792313617419357929919885147015760602644662L,
                   'timestamp': 2L,
                   'gaslimit': 16777216L,
                   'number': 768L,
                   'difficulty': 565222794527730373379072786348411718562863470688369141095402336226947079297792115994616109365L,
                   'coinbase': 244687034288125203496486448490407391986876152250L
                  }
        pos_world = {
                            87579061662017136990230301793909925042452127430L: {
                             'nonce': 0L,
                             'balance': 4722366482869645213696L,
                             'code': 'A@@C@C@B{@b\x0bwRU',
                             'storage': {
                             }
                            }
                           }

        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)           
        platform.create_account(address=87579061662017136990230301793909925042452127430L, 
                                balance=4722366482869645213696L, 
                                code='A@@C@C@B{@b\x0bwRU', 
                                storage={
                                        }
                                )        
        address = 87579061662017136990230301793909925042452127430L
        origin = 1170859069862169782511871033392474246841492526721L
        price = 72057594037927936L
        data = ''
        caller = 1170859069862169782511871033392474246841492526721L
        value = 4722366482869645213696L        
        platform.transaction(address, origin, price, data, caller, value, header)
        
        throw = False
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
