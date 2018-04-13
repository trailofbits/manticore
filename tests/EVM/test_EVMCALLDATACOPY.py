
import struct
import string
import unittest
import json
from manticore.platforms import evm
from manticore.core import state
from manticore.core.smtlib import Operators, ConstraintSet
import os


class EVMTest_CALLDATACOPY(unittest.TestCase):
    _multiprocess_can_split_ = True
    maxDiff=None 
    def _execute(self, new_vm):
        last_returned = None
        last_exception = None
        try:
            new_vm.execute()
        except evm.Stop:
            last_exception = "STOP"
        except evm.NotEnoughGas:
            last_exception = "OOG"
        except evm.StackUnderflow:
            last_exception = "INSUFICIENT STACK"
        except evm.InvalidOpcode:
            last_exception = "INVALID"
        except evm.SelfDestruct:
            last_exception = "SUICIDED"
        except evm.Return as e:
            last_exception = "RETURN"
            last_returned = e.data
        except evm.Revert:
            last_exception = "REVERT"
            
        return last_exception, last_returned

    def test_CALLDATACOPY(self):
            #Make the constraint store
            constraints = ConstraintSet()
            #make the ethereum world state
            world = evm.EVMWorld(constraints)

            address=0x222222222222222222222222222222222222200
            caller=origin=0x111111111111111111111111111111111111100
            price=0
            value=10000
            bytecode='7'
            data = map(chr, range(ord('A'), ord('Z')))
            header = { 'coinbase': 0,
                        'timestamp': 0,
                        'number': 0,
                        'difficulty': 0,
                        'gaslimit': 0,
                        }
            gas = 1000000

            new_vm = evm.EVM(constraints, address, origin, price, data, caller, value, bytecode, header, gas=gas, global_storage=world.storage)
            new_vm._push(9)
            new_vm._push(9)
            new_vm._push(0)
            last_exception, last_returned = self._execute(new_vm)
            self.assertEqual(last_exception, None)
            self.assertEqual(new_vm.pc, 1)
            self.assertEqual(new_vm.stack, [])
            self.assertEqual(list(new_vm.memory.read(0, 9)), [ord(c) for c in string.ascii_uppercase[9:18]])

    def test_CALLDATACOPY_overflow(self):
            #Make the constraint store
            constraints = ConstraintSet()
            #make the ethereum world state
            world = evm.EVMWorld(constraints)

            address=0x222222222222222222222222222222222222200
            caller=origin=0x111111111111111111111111111111111111100
            price=0
            value=10000
            bytecode='7'
            data = string.ascii_uppercase
            header = { 'coinbase': 0,
                        'timestamp': 0,
                        'number': 0,
                        'difficulty': 0,
                        'gaslimit': 0,
                        }
            gas = 1000000

            new_vm = evm.EVM(constraints, address, origin, price, data, caller, value, bytecode, header, gas=gas, global_storage=world.storage)
            length = 9
            new_vm._push(length) # length
            new_vm._push(999999) # offset
            new_vm._push(0)      # memoffset
            last_exception, last_returned = self._execute(new_vm)
            self.assertEqual(last_exception, None)
            self.assertEqual(new_vm.pc, 1)
            self.assertEqual(new_vm.stack, [])
            # we should have written 9 bytes ..
            self.assertEqual(len(new_vm.memory.items()), length)
            # .. and they should have all been zero
            self.assertTrue(all(val == 0 for addr, val in new_vm.memory.items()))

    def test_CALLDATACOPY_partialoverflow(self):
            #Make the constraint store
            constraints = ConstraintSet()
            #make the ethereum world state
            world = evm.EVMWorld(constraints)

            address=0x222222222222222222222222222222222222200
            caller=origin=0x111111111111111111111111111111111111100
            price=0
            value=10000
            bytecode='7'
            data = string.ascii_uppercase
            header = { 'coinbase': 0,
                        'timestamp': 0,
                        'number': 0,
                        'difficulty': 0,
                        'gaslimit': 0,
                        }
            gas = 10000000000

            new_vm = evm.EVM(constraints, address, origin, price, data, caller, value, bytecode, header, gas=gas, global_storage=world.storage)
            offset = 23
            remainder = len(data) - offset
            new_vm._push(9999)   # size
            new_vm._push(offset) # data_offset
            new_vm._push(0)      # mem_offset
            last_exception, last_returned = self._execute(new_vm)
            self.assertEqual(last_exception, None)
            self.assertEqual(new_vm.pc, 1)
            self.assertEqual(new_vm.stack, [])
            self.assertEqual(list(new_vm.memory.read(0, 3)), [ord(c) for c in data[-remainder:]])
            # make sure all 9999 bytes were written (even though they're mostly zeroes)
            self.assertEqual(len(new_vm.memory.items()), 9999)
            # make sure all but the first |remainder| items are 0
            self.assertTrue(all(val == 0 for addr, val in new_vm.memory.items() if addr > remainder - 1))
            # and make sure there's 9999-remainder of them
            self.assertEqual(sum(1 for addr, _ in new_vm.memory.items() if addr > remainder - 1), 9999-remainder)

if __name__ == '__main__':
    unittest.main()
