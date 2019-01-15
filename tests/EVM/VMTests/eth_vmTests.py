
#Taken from /home/felipe/Projects/manticore/tests/auto/tests/VMTests/vmTests
import struct
import unittest
import json
import os
from binascii import unhexlify
from manticore.platforms import evm
from manticore.core import state
from manticore.core.smtlib import Operators, ConstraintSet
from manticore.core.smtlib.visitors import to_constant
import sha3
import rlp
from rlp.sedes import (
    CountableList,
    BigEndianInt,
    Binary,
)
class Log(rlp.Serializable):
    fields = [
        ('address', Binary.fixed_length(20, allow_empty=True)),
        ('topics', CountableList(BigEndianInt(32))),
        ('data', Binary())
    ]

evm.DEFAULT_FORK = "frontier"
class EVMTest_vmTests(unittest.TestCase):
    _multiprocess_can_split_ = True
    maxDiff=None 


    def test_suicide(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: suicide.json
            sha256sum: 1aa0a61de3c9576faf6ac4f002626210a5315d3132d032162b2934d304a60c1f
            Code: CALLER
                  SELFDESTRUCT
        '''    
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber=0, timestamp=1, difficulty=256, coinbase=244687034288125203496486448490407391986876152250, gaslimit=1000000)
    
        bytecode = unhexlify('33ff')
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=100000000000000000000000,
                             code=bytecode,
                             nonce=0
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f3947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        gas = 100000

        # open a fake tx, no funds send
        world._open_transaction('CALL', address, price, data, caller, value, gas=gas)

        result = None
        returndata = b''
        try:
            while True:
                world.current_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')
        #Add pos checks for account 0xcd1722f3947def4cf144679da39c4c32bdc35681
        #check nonce, balance, code
        self.assertEqual(world.get_nonce(0xcd1722f3947def4cf144679da39c4c32bdc35681), 0)
        self.assertEqual(to_constant(world.get_balance(0xcd1722f3947def4cf144679da39c4c32bdc35681)), 100000000000000000000000)
        self.assertEqual(world.get_code(0xcd1722f3947def4cf144679da39c4c32bdc35681), unhexlify(''))
        #check outs
        self.assertEqual(returndata, unhexlify(''))
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
        
        # test used gas
        self.assertEqual(to_constant(world.current_vm.gas), 99998)

if __name__ == '__main__':
    unittest.main()
