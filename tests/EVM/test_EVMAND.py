
import struct
import unittest
import json
from manticore.platforms import evm
from manticore.core import state
from manticore.core.smtlib import Operators, ConstraintSet
import os


class EVMTest_AND(unittest.TestCase):
    _multiprocess_can_split_ = True
    maxDiff=None 
    def _execute(self, new_vm):
        last_returned = None
        last_exception = None
        try:
            new_vm.execute()
        except evm.Stop, e:
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

    def test_AND_1(self):
            #Make the constraint store
            constraints = ConstraintSet()
            #make the ethereum world state
            world = evm.EVMWorld(constraints)

            address=0x222222222222222222222222222222222222200
            caller=origin=0x111111111111111111111111111111111111100
            price=0
            value=10000
            bytecode='\x16'
            data = 'AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA'
            header = { 'coinbase': 0,
                        'timestamp': 0,
                        'number': 0,
                        'difficulty': 0,
                        'gaslimit': 0,
                        }
            gas = 1000000

            new_vm = evm.EVM(constraints, address, origin, price, data, caller, value, bytecode, header, gas=gas, global_storage=world.storage)
            new_vm._push(115792089237316195423570985008687907853269984665640564039457584007913129639935L)
            new_vm._push(115792089237316195423570985008687907853269984665640564039457584007913129639935L)
            last_exception, last_returned = self._execute(new_vm)
            self.assertEqual(last_exception, None)
            self.assertEqual(new_vm.pc, 1)
            self.assertEqual(new_vm.stack, [115792089237316195423570985008687907853269984665640564039457584007913129639935L])

    def test_AND_2(self):
            #Make the constraint store
            constraints = ConstraintSet()
            #make the ethereum world state
            world = evm.EVMWorld(constraints)

            address=0x222222222222222222222222222222222222200
            caller=origin=0x111111111111111111111111111111111111100
            price=0
            value=10000
            bytecode='\x16'
            data = 'AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA'
            header = { 'coinbase': 0,
                        'timestamp': 0,
                        'number': 0,
                        'difficulty': 0,
                        'gaslimit': 0,
                        }
            gas = 1000000

            new_vm = evm.EVM(constraints, address, origin, price, data, caller, value, bytecode, header, gas=gas, global_storage=world.storage)
            new_vm._push(115792089237316195423570985008687907853269984665640564039457584007913129639935L)
            new_vm._push(0)
            last_exception, last_returned = self._execute(new_vm)
            self.assertEqual(last_exception, None)
            self.assertEqual(new_vm.pc, 1)
            self.assertEqual(new_vm.stack, [0L])

    def test_AND_3(self):
            #Make the constraint store
            constraints = ConstraintSet()
            #make the ethereum world state
            world = evm.EVMWorld(constraints)

            address=0x222222222222222222222222222222222222200
            caller=origin=0x111111111111111111111111111111111111100
            price=0
            value=10000
            bytecode='\x16'
            data = 'AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA'
            header = { 'coinbase': 0,
                        'timestamp': 0,
                        'number': 0,
                        'difficulty': 0,
                        'gaslimit': 0,
                        }
            gas = 1000000

            new_vm = evm.EVM(constraints, address, origin, price, data, caller, value, bytecode, header, gas=gas, global_storage=world.storage)
            new_vm._push(115792089237316195423570985008687907853269984665640564039457584007913129639935L)
            new_vm._push(1)
            last_exception, last_returned = self._execute(new_vm)
            self.assertEqual(last_exception, None)
            self.assertEqual(new_vm.pc, 1)
            self.assertEqual(new_vm.stack, [1L])

    def test_AND_4(self):
            #Make the constraint store
            constraints = ConstraintSet()
            #make the ethereum world state
            world = evm.EVMWorld(constraints)

            address=0x222222222222222222222222222222222222200
            caller=origin=0x111111111111111111111111111111111111100
            price=0
            value=10000
            bytecode='\x16'
            data = 'AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA'
            header = { 'coinbase': 0,
                        'timestamp': 0,
                        'number': 0,
                        'difficulty': 0,
                        'gaslimit': 0,
                        }
            gas = 1000000

            new_vm = evm.EVM(constraints, address, origin, price, data, caller, value, bytecode, header, gas=gas, global_storage=world.storage)
            new_vm._push(115792089237316195423570985008687907853269984665640564039457584007913129639935L)
            new_vm._push(57896044618658097711785492504343953926634992332820282019728792003956564819952L)
            last_exception, last_returned = self._execute(new_vm)
            self.assertEqual(last_exception, None)
            self.assertEqual(new_vm.pc, 1)
            self.assertEqual(new_vm.stack, [57896044618658097711785492504343953926634992332820282019728792003956564819952L])

    def test_AND_5(self):
            #Make the constraint store
            constraints = ConstraintSet()
            #make the ethereum world state
            world = evm.EVMWorld(constraints)

            address=0x222222222222222222222222222222222222200
            caller=origin=0x111111111111111111111111111111111111100
            price=0
            value=10000
            bytecode='\x16'
            data = 'AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA'
            header = { 'coinbase': 0,
                        'timestamp': 0,
                        'number': 0,
                        'difficulty': 0,
                        'gaslimit': 0,
                        }
            gas = 1000000

            new_vm = evm.EVM(constraints, address, origin, price, data, caller, value, bytecode, header, gas=gas, global_storage=world.storage)
            new_vm._push(115792089237316195423570985008687907853269984665640564039457584007913129639935L)
            new_vm._push(3618502788666131106986593281521497120414687020801267626233049500247285301263L)
            last_exception, last_returned = self._execute(new_vm)
            self.assertEqual(last_exception, None)
            self.assertEqual(new_vm.pc, 1)
            self.assertEqual(new_vm.stack, [3618502788666131106986593281521497120414687020801267626233049500247285301263L])

    def test_AND_6(self):
            #Make the constraint store
            constraints = ConstraintSet()
            #make the ethereum world state
            world = evm.EVMWorld(constraints)

            address=0x222222222222222222222222222222222222200
            caller=origin=0x111111111111111111111111111111111111100
            price=0
            value=10000
            bytecode='\x16'
            data = 'AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA'
            header = { 'coinbase': 0,
                        'timestamp': 0,
                        'number': 0,
                        'difficulty': 0,
                        'gaslimit': 0,
                        }
            gas = 1000000

            new_vm = evm.EVM(constraints, address, origin, price, data, caller, value, bytecode, header, gas=gas, global_storage=world.storage)
            new_vm._push(115792089237316195423570985008687907853269984665640564039457584007913129639935L)
            new_vm._push(16)
            last_exception, last_returned = self._execute(new_vm)
            self.assertEqual(last_exception, None)
            self.assertEqual(new_vm.pc, 1)
            self.assertEqual(new_vm.stack, [16L])

    def test_AND_7(self):
            #Make the constraint store
            constraints = ConstraintSet()
            #make the ethereum world state
            world = evm.EVMWorld(constraints)

            address=0x222222222222222222222222222222222222200
            caller=origin=0x111111111111111111111111111111111111100
            price=0
            value=10000
            bytecode='\x16'
            data = 'AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA'
            header = { 'coinbase': 0,
                        'timestamp': 0,
                        'number': 0,
                        'difficulty': 0,
                        'gaslimit': 0,
                        }
            gas = 1000000

            new_vm = evm.EVM(constraints, address, origin, price, data, caller, value, bytecode, header, gas=gas, global_storage=world.storage)
            new_vm._push(115792089237316195423570985008687907853269984665640564039457584007913129639935L)
            new_vm._push(32)
            last_exception, last_returned = self._execute(new_vm)
            self.assertEqual(last_exception, None)
            self.assertEqual(new_vm.pc, 1)
            self.assertEqual(new_vm.stack, [32L])

    def test_AND_8(self):
            #Make the constraint store
            constraints = ConstraintSet()
            #make the ethereum world state
            world = evm.EVMWorld(constraints)

            address=0x222222222222222222222222222222222222200
            caller=origin=0x111111111111111111111111111111111111100
            price=0
            value=10000
            bytecode='\x16'
            data = 'AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA'
            header = { 'coinbase': 0,
                        'timestamp': 0,
                        'number': 0,
                        'difficulty': 0,
                        'gaslimit': 0,
                        }
            gas = 1000000

            new_vm = evm.EVM(constraints, address, origin, price, data, caller, value, bytecode, header, gas=gas, global_storage=world.storage)
            new_vm._push(115792089237316195423570985008687907853269984665640564039457584007913129639935L)
            new_vm._push(48)
            last_exception, last_returned = self._execute(new_vm)
            self.assertEqual(last_exception, None)
            self.assertEqual(new_vm.pc, 1)
            self.assertEqual(new_vm.stack, [48L])

    def test_AND_9(self):
            #Make the constraint store
            constraints = ConstraintSet()
            #make the ethereum world state
            world = evm.EVMWorld(constraints)

            address=0x222222222222222222222222222222222222200
            caller=origin=0x111111111111111111111111111111111111100
            price=0
            value=10000
            bytecode='\x16'
            data = 'AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA'
            header = { 'coinbase': 0,
                        'timestamp': 0,
                        'number': 0,
                        'difficulty': 0,
                        'gaslimit': 0,
                        }
            gas = 1000000

            new_vm = evm.EVM(constraints, address, origin, price, data, caller, value, bytecode, header, gas=gas, global_storage=world.storage)
            new_vm._push(115792089237316195423570985008687907853269984665640564039457584007913129639935L)
            new_vm._push(6089590155545428825848686802984512581899718912L)
            last_exception, last_returned = self._execute(new_vm)
            self.assertEqual(last_exception, None)
            self.assertEqual(new_vm.pc, 1)
            self.assertEqual(new_vm.stack, [6089590155545428825848686802984512581899718912L])

    def test_AND_10(self):
            #Make the constraint store
            constraints = ConstraintSet()
            #make the ethereum world state
            world = evm.EVMWorld(constraints)

            address=0x222222222222222222222222222222222222200
            caller=origin=0x111111111111111111111111111111111111100
            price=0
            value=10000
            bytecode='\x16'
            data = 'AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA'
            header = { 'coinbase': 0,
                        'timestamp': 0,
                        'number': 0,
                        'difficulty': 0,
                        'gaslimit': 0,
                        }
            gas = 1000000

            new_vm = evm.EVM(constraints, address, origin, price, data, caller, value, bytecode, header, gas=gas, global_storage=world.storage)
            new_vm._push(0)
            new_vm._push(115792089237316195423570985008687907853269984665640564039457584007913129639935L)
            last_exception, last_returned = self._execute(new_vm)
            self.assertEqual(last_exception, None)
            self.assertEqual(new_vm.pc, 1)
            self.assertEqual(new_vm.stack, [0L])

    def test_AND_11(self):
            #Make the constraint store
            constraints = ConstraintSet()
            #make the ethereum world state
            world = evm.EVMWorld(constraints)

            address=0x222222222222222222222222222222222222200
            caller=origin=0x111111111111111111111111111111111111100
            price=0
            value=10000
            bytecode='\x16'
            data = 'AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA'
            header = { 'coinbase': 0,
                        'timestamp': 0,
                        'number': 0,
                        'difficulty': 0,
                        'gaslimit': 0,
                        }
            gas = 1000000

            new_vm = evm.EVM(constraints, address, origin, price, data, caller, value, bytecode, header, gas=gas, global_storage=world.storage)
            new_vm._push(0)
            new_vm._push(0)
            last_exception, last_returned = self._execute(new_vm)
            self.assertEqual(last_exception, None)
            self.assertEqual(new_vm.pc, 1)
            self.assertEqual(new_vm.stack, [0])

    def test_AND_12(self):
            #Make the constraint store
            constraints = ConstraintSet()
            #make the ethereum world state
            world = evm.EVMWorld(constraints)

            address=0x222222222222222222222222222222222222200
            caller=origin=0x111111111111111111111111111111111111100
            price=0
            value=10000
            bytecode='\x16'
            data = 'AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA'
            header = { 'coinbase': 0,
                        'timestamp': 0,
                        'number': 0,
                        'difficulty': 0,
                        'gaslimit': 0,
                        }
            gas = 1000000

            new_vm = evm.EVM(constraints, address, origin, price, data, caller, value, bytecode, header, gas=gas, global_storage=world.storage)
            new_vm._push(0)
            new_vm._push(1)
            last_exception, last_returned = self._execute(new_vm)
            self.assertEqual(last_exception, None)
            self.assertEqual(new_vm.pc, 1)
            self.assertEqual(new_vm.stack, [0])

    def test_AND_13(self):
            #Make the constraint store
            constraints = ConstraintSet()
            #make the ethereum world state
            world = evm.EVMWorld(constraints)

            address=0x222222222222222222222222222222222222200
            caller=origin=0x111111111111111111111111111111111111100
            price=0
            value=10000
            bytecode='\x16'
            data = 'AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA'
            header = { 'coinbase': 0,
                        'timestamp': 0,
                        'number': 0,
                        'difficulty': 0,
                        'gaslimit': 0,
                        }
            gas = 1000000

            new_vm = evm.EVM(constraints, address, origin, price, data, caller, value, bytecode, header, gas=gas, global_storage=world.storage)
            new_vm._push(0)
            new_vm._push(57896044618658097711785492504343953926634992332820282019728792003956564819952L)
            last_exception, last_returned = self._execute(new_vm)
            self.assertEqual(last_exception, None)
            self.assertEqual(new_vm.pc, 1)
            self.assertEqual(new_vm.stack, [0L])

    def test_AND_14(self):
            #Make the constraint store
            constraints = ConstraintSet()
            #make the ethereum world state
            world = evm.EVMWorld(constraints)

            address=0x222222222222222222222222222222222222200
            caller=origin=0x111111111111111111111111111111111111100
            price=0
            value=10000
            bytecode='\x16'
            data = 'AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA'
            header = { 'coinbase': 0,
                        'timestamp': 0,
                        'number': 0,
                        'difficulty': 0,
                        'gaslimit': 0,
                        }
            gas = 1000000

            new_vm = evm.EVM(constraints, address, origin, price, data, caller, value, bytecode, header, gas=gas, global_storage=world.storage)
            new_vm._push(0)
            new_vm._push(3618502788666131106986593281521497120414687020801267626233049500247285301263L)
            last_exception, last_returned = self._execute(new_vm)
            self.assertEqual(last_exception, None)
            self.assertEqual(new_vm.pc, 1)
            self.assertEqual(new_vm.stack, [0L])

    def test_AND_15(self):
            #Make the constraint store
            constraints = ConstraintSet()
            #make the ethereum world state
            world = evm.EVMWorld(constraints)

            address=0x222222222222222222222222222222222222200
            caller=origin=0x111111111111111111111111111111111111100
            price=0
            value=10000
            bytecode='\x16'
            data = 'AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA'
            header = { 'coinbase': 0,
                        'timestamp': 0,
                        'number': 0,
                        'difficulty': 0,
                        'gaslimit': 0,
                        }
            gas = 1000000

            new_vm = evm.EVM(constraints, address, origin, price, data, caller, value, bytecode, header, gas=gas, global_storage=world.storage)
            new_vm._push(0)
            new_vm._push(16)
            last_exception, last_returned = self._execute(new_vm)
            self.assertEqual(last_exception, None)
            self.assertEqual(new_vm.pc, 1)
            self.assertEqual(new_vm.stack, [0])

    def test_AND_16(self):
            #Make the constraint store
            constraints = ConstraintSet()
            #make the ethereum world state
            world = evm.EVMWorld(constraints)

            address=0x222222222222222222222222222222222222200
            caller=origin=0x111111111111111111111111111111111111100
            price=0
            value=10000
            bytecode='\x16'
            data = 'AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA'
            header = { 'coinbase': 0,
                        'timestamp': 0,
                        'number': 0,
                        'difficulty': 0,
                        'gaslimit': 0,
                        }
            gas = 1000000

            new_vm = evm.EVM(constraints, address, origin, price, data, caller, value, bytecode, header, gas=gas, global_storage=world.storage)
            new_vm._push(0)
            new_vm._push(32)
            last_exception, last_returned = self._execute(new_vm)
            self.assertEqual(last_exception, None)
            self.assertEqual(new_vm.pc, 1)
            self.assertEqual(new_vm.stack, [0])

    def test_AND_17(self):
            #Make the constraint store
            constraints = ConstraintSet()
            #make the ethereum world state
            world = evm.EVMWorld(constraints)

            address=0x222222222222222222222222222222222222200
            caller=origin=0x111111111111111111111111111111111111100
            price=0
            value=10000
            bytecode='\x16'
            data = 'AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA'
            header = { 'coinbase': 0,
                        'timestamp': 0,
                        'number': 0,
                        'difficulty': 0,
                        'gaslimit': 0,
                        }
            gas = 1000000

            new_vm = evm.EVM(constraints, address, origin, price, data, caller, value, bytecode, header, gas=gas, global_storage=world.storage)
            new_vm._push(0)
            new_vm._push(48)
            last_exception, last_returned = self._execute(new_vm)
            self.assertEqual(last_exception, None)
            self.assertEqual(new_vm.pc, 1)
            self.assertEqual(new_vm.stack, [0])

    def test_AND_18(self):
            #Make the constraint store
            constraints = ConstraintSet()
            #make the ethereum world state
            world = evm.EVMWorld(constraints)

            address=0x222222222222222222222222222222222222200
            caller=origin=0x111111111111111111111111111111111111100
            price=0
            value=10000
            bytecode='\x16'
            data = 'AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA'
            header = { 'coinbase': 0,
                        'timestamp': 0,
                        'number': 0,
                        'difficulty': 0,
                        'gaslimit': 0,
                        }
            gas = 1000000

            new_vm = evm.EVM(constraints, address, origin, price, data, caller, value, bytecode, header, gas=gas, global_storage=world.storage)
            new_vm._push(0)
            new_vm._push(6089590155545428825848686802984512581899718912L)
            last_exception, last_returned = self._execute(new_vm)
            self.assertEqual(last_exception, None)
            self.assertEqual(new_vm.pc, 1)
            self.assertEqual(new_vm.stack, [0L])

    def test_AND_19(self):
            #Make the constraint store
            constraints = ConstraintSet()
            #make the ethereum world state
            world = evm.EVMWorld(constraints)

            address=0x222222222222222222222222222222222222200
            caller=origin=0x111111111111111111111111111111111111100
            price=0
            value=10000
            bytecode='\x16'
            data = 'AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA'
            header = { 'coinbase': 0,
                        'timestamp': 0,
                        'number': 0,
                        'difficulty': 0,
                        'gaslimit': 0,
                        }
            gas = 1000000

            new_vm = evm.EVM(constraints, address, origin, price, data, caller, value, bytecode, header, gas=gas, global_storage=world.storage)
            new_vm._push(1)
            new_vm._push(115792089237316195423570985008687907853269984665640564039457584007913129639935L)
            last_exception, last_returned = self._execute(new_vm)
            self.assertEqual(last_exception, None)
            self.assertEqual(new_vm.pc, 1)
            self.assertEqual(new_vm.stack, [1L])

    def test_AND_20(self):
            #Make the constraint store
            constraints = ConstraintSet()
            #make the ethereum world state
            world = evm.EVMWorld(constraints)

            address=0x222222222222222222222222222222222222200
            caller=origin=0x111111111111111111111111111111111111100
            price=0
            value=10000
            bytecode='\x16'
            data = 'AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA'
            header = { 'coinbase': 0,
                        'timestamp': 0,
                        'number': 0,
                        'difficulty': 0,
                        'gaslimit': 0,
                        }
            gas = 1000000

            new_vm = evm.EVM(constraints, address, origin, price, data, caller, value, bytecode, header, gas=gas, global_storage=world.storage)
            new_vm._push(1)
            new_vm._push(0)
            last_exception, last_returned = self._execute(new_vm)
            self.assertEqual(last_exception, None)
            self.assertEqual(new_vm.pc, 1)
            self.assertEqual(new_vm.stack, [0])

    def test_AND_21(self):
            #Make the constraint store
            constraints = ConstraintSet()
            #make the ethereum world state
            world = evm.EVMWorld(constraints)

            address=0x222222222222222222222222222222222222200
            caller=origin=0x111111111111111111111111111111111111100
            price=0
            value=10000
            bytecode='\x16'
            data = 'AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA'
            header = { 'coinbase': 0,
                        'timestamp': 0,
                        'number': 0,
                        'difficulty': 0,
                        'gaslimit': 0,
                        }
            gas = 1000000

            new_vm = evm.EVM(constraints, address, origin, price, data, caller, value, bytecode, header, gas=gas, global_storage=world.storage)
            new_vm._push(1)
            new_vm._push(1)
            last_exception, last_returned = self._execute(new_vm)
            self.assertEqual(last_exception, None)
            self.assertEqual(new_vm.pc, 1)
            self.assertEqual(new_vm.stack, [1])

    def test_AND_22(self):
            #Make the constraint store
            constraints = ConstraintSet()
            #make the ethereum world state
            world = evm.EVMWorld(constraints)

            address=0x222222222222222222222222222222222222200
            caller=origin=0x111111111111111111111111111111111111100
            price=0
            value=10000
            bytecode='\x16'
            data = 'AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA'
            header = { 'coinbase': 0,
                        'timestamp': 0,
                        'number': 0,
                        'difficulty': 0,
                        'gaslimit': 0,
                        }
            gas = 1000000

            new_vm = evm.EVM(constraints, address, origin, price, data, caller, value, bytecode, header, gas=gas, global_storage=world.storage)
            new_vm._push(1)
            new_vm._push(57896044618658097711785492504343953926634992332820282019728792003956564819952L)
            last_exception, last_returned = self._execute(new_vm)
            self.assertEqual(last_exception, None)
            self.assertEqual(new_vm.pc, 1)
            self.assertEqual(new_vm.stack, [0L])

    def test_AND_23(self):
            #Make the constraint store
            constraints = ConstraintSet()
            #make the ethereum world state
            world = evm.EVMWorld(constraints)

            address=0x222222222222222222222222222222222222200
            caller=origin=0x111111111111111111111111111111111111100
            price=0
            value=10000
            bytecode='\x16'
            data = 'AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA'
            header = { 'coinbase': 0,
                        'timestamp': 0,
                        'number': 0,
                        'difficulty': 0,
                        'gaslimit': 0,
                        }
            gas = 1000000

            new_vm = evm.EVM(constraints, address, origin, price, data, caller, value, bytecode, header, gas=gas, global_storage=world.storage)
            new_vm._push(1)
            new_vm._push(3618502788666131106986593281521497120414687020801267626233049500247285301263L)
            last_exception, last_returned = self._execute(new_vm)
            self.assertEqual(last_exception, None)
            self.assertEqual(new_vm.pc, 1)
            self.assertEqual(new_vm.stack, [1L])

    def test_AND_24(self):
            #Make the constraint store
            constraints = ConstraintSet()
            #make the ethereum world state
            world = evm.EVMWorld(constraints)

            address=0x222222222222222222222222222222222222200
            caller=origin=0x111111111111111111111111111111111111100
            price=0
            value=10000
            bytecode='\x16'
            data = 'AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA'
            header = { 'coinbase': 0,
                        'timestamp': 0,
                        'number': 0,
                        'difficulty': 0,
                        'gaslimit': 0,
                        }
            gas = 1000000

            new_vm = evm.EVM(constraints, address, origin, price, data, caller, value, bytecode, header, gas=gas, global_storage=world.storage)
            new_vm._push(1)
            new_vm._push(16)
            last_exception, last_returned = self._execute(new_vm)
            self.assertEqual(last_exception, None)
            self.assertEqual(new_vm.pc, 1)
            self.assertEqual(new_vm.stack, [0])

    def test_AND_25(self):
            #Make the constraint store
            constraints = ConstraintSet()
            #make the ethereum world state
            world = evm.EVMWorld(constraints)

            address=0x222222222222222222222222222222222222200
            caller=origin=0x111111111111111111111111111111111111100
            price=0
            value=10000
            bytecode='\x16'
            data = 'AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA'
            header = { 'coinbase': 0,
                        'timestamp': 0,
                        'number': 0,
                        'difficulty': 0,
                        'gaslimit': 0,
                        }
            gas = 1000000

            new_vm = evm.EVM(constraints, address, origin, price, data, caller, value, bytecode, header, gas=gas, global_storage=world.storage)
            new_vm._push(1)
            new_vm._push(32)
            last_exception, last_returned = self._execute(new_vm)
            self.assertEqual(last_exception, None)
            self.assertEqual(new_vm.pc, 1)
            self.assertEqual(new_vm.stack, [0])

    def test_AND_26(self):
            #Make the constraint store
            constraints = ConstraintSet()
            #make the ethereum world state
            world = evm.EVMWorld(constraints)

            address=0x222222222222222222222222222222222222200
            caller=origin=0x111111111111111111111111111111111111100
            price=0
            value=10000
            bytecode='\x16'
            data = 'AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA'
            header = { 'coinbase': 0,
                        'timestamp': 0,
                        'number': 0,
                        'difficulty': 0,
                        'gaslimit': 0,
                        }
            gas = 1000000

            new_vm = evm.EVM(constraints, address, origin, price, data, caller, value, bytecode, header, gas=gas, global_storage=world.storage)
            new_vm._push(1)
            new_vm._push(48)
            last_exception, last_returned = self._execute(new_vm)
            self.assertEqual(last_exception, None)
            self.assertEqual(new_vm.pc, 1)
            self.assertEqual(new_vm.stack, [0])

    def test_AND_27(self):
            #Make the constraint store
            constraints = ConstraintSet()
            #make the ethereum world state
            world = evm.EVMWorld(constraints)

            address=0x222222222222222222222222222222222222200
            caller=origin=0x111111111111111111111111111111111111100
            price=0
            value=10000
            bytecode='\x16'
            data = 'AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA'
            header = { 'coinbase': 0,
                        'timestamp': 0,
                        'number': 0,
                        'difficulty': 0,
                        'gaslimit': 0,
                        }
            gas = 1000000

            new_vm = evm.EVM(constraints, address, origin, price, data, caller, value, bytecode, header, gas=gas, global_storage=world.storage)
            new_vm._push(1)
            new_vm._push(6089590155545428825848686802984512581899718912L)
            last_exception, last_returned = self._execute(new_vm)
            self.assertEqual(last_exception, None)
            self.assertEqual(new_vm.pc, 1)
            self.assertEqual(new_vm.stack, [0L])

    def test_AND_28(self):
            #Make the constraint store
            constraints = ConstraintSet()
            #make the ethereum world state
            world = evm.EVMWorld(constraints)

            address=0x222222222222222222222222222222222222200
            caller=origin=0x111111111111111111111111111111111111100
            price=0
            value=10000
            bytecode='\x16'
            data = 'AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA'
            header = { 'coinbase': 0,
                        'timestamp': 0,
                        'number': 0,
                        'difficulty': 0,
                        'gaslimit': 0,
                        }
            gas = 1000000

            new_vm = evm.EVM(constraints, address, origin, price, data, caller, value, bytecode, header, gas=gas, global_storage=world.storage)
            new_vm._push(57896044618658097711785492504343953926634992332820282019728792003956564819952L)
            new_vm._push(115792089237316195423570985008687907853269984665640564039457584007913129639935L)
            last_exception, last_returned = self._execute(new_vm)
            self.assertEqual(last_exception, None)
            self.assertEqual(new_vm.pc, 1)
            self.assertEqual(new_vm.stack, [57896044618658097711785492504343953926634992332820282019728792003956564819952L])

    def test_AND_29(self):
            #Make the constraint store
            constraints = ConstraintSet()
            #make the ethereum world state
            world = evm.EVMWorld(constraints)

            address=0x222222222222222222222222222222222222200
            caller=origin=0x111111111111111111111111111111111111100
            price=0
            value=10000
            bytecode='\x16'
            data = 'AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA'
            header = { 'coinbase': 0,
                        'timestamp': 0,
                        'number': 0,
                        'difficulty': 0,
                        'gaslimit': 0,
                        }
            gas = 1000000

            new_vm = evm.EVM(constraints, address, origin, price, data, caller, value, bytecode, header, gas=gas, global_storage=world.storage)
            new_vm._push(57896044618658097711785492504343953926634992332820282019728792003956564819952L)
            new_vm._push(0)
            last_exception, last_returned = self._execute(new_vm)
            self.assertEqual(last_exception, None)
            self.assertEqual(new_vm.pc, 1)
            self.assertEqual(new_vm.stack, [0L])

    def test_AND_30(self):
            #Make the constraint store
            constraints = ConstraintSet()
            #make the ethereum world state
            world = evm.EVMWorld(constraints)

            address=0x222222222222222222222222222222222222200
            caller=origin=0x111111111111111111111111111111111111100
            price=0
            value=10000
            bytecode='\x16'
            data = 'AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA'
            header = { 'coinbase': 0,
                        'timestamp': 0,
                        'number': 0,
                        'difficulty': 0,
                        'gaslimit': 0,
                        }
            gas = 1000000

            new_vm = evm.EVM(constraints, address, origin, price, data, caller, value, bytecode, header, gas=gas, global_storage=world.storage)
            new_vm._push(57896044618658097711785492504343953926634992332820282019728792003956564819952L)
            new_vm._push(1)
            last_exception, last_returned = self._execute(new_vm)
            self.assertEqual(last_exception, None)
            self.assertEqual(new_vm.pc, 1)
            self.assertEqual(new_vm.stack, [0L])

    def test_AND_31(self):
            #Make the constraint store
            constraints = ConstraintSet()
            #make the ethereum world state
            world = evm.EVMWorld(constraints)

            address=0x222222222222222222222222222222222222200
            caller=origin=0x111111111111111111111111111111111111100
            price=0
            value=10000
            bytecode='\x16'
            data = 'AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA'
            header = { 'coinbase': 0,
                        'timestamp': 0,
                        'number': 0,
                        'difficulty': 0,
                        'gaslimit': 0,
                        }
            gas = 1000000

            new_vm = evm.EVM(constraints, address, origin, price, data, caller, value, bytecode, header, gas=gas, global_storage=world.storage)
            new_vm._push(57896044618658097711785492504343953926634992332820282019728792003956564819952L)
            new_vm._push(57896044618658097711785492504343953926634992332820282019728792003956564819952L)
            last_exception, last_returned = self._execute(new_vm)
            self.assertEqual(last_exception, None)
            self.assertEqual(new_vm.pc, 1)
            self.assertEqual(new_vm.stack, [57896044618658097711785492504343953926634992332820282019728792003956564819952L])

    def test_AND_32(self):
            #Make the constraint store
            constraints = ConstraintSet()
            #make the ethereum world state
            world = evm.EVMWorld(constraints)

            address=0x222222222222222222222222222222222222200
            caller=origin=0x111111111111111111111111111111111111100
            price=0
            value=10000
            bytecode='\x16'
            data = 'AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA'
            header = { 'coinbase': 0,
                        'timestamp': 0,
                        'number': 0,
                        'difficulty': 0,
                        'gaslimit': 0,
                        }
            gas = 1000000

            new_vm = evm.EVM(constraints, address, origin, price, data, caller, value, bytecode, header, gas=gas, global_storage=world.storage)
            new_vm._push(57896044618658097711785492504343953926634992332820282019728792003956564819952L)
            new_vm._push(3618502788666131106986593281521497120414687020801267626233049500247285301263L)
            last_exception, last_returned = self._execute(new_vm)
            self.assertEqual(last_exception, None)
            self.assertEqual(new_vm.pc, 1)
            self.assertEqual(new_vm.stack, [3618502788666131106986593281521497120414687020801267626233049500247285301248L])

    def test_AND_33(self):
            #Make the constraint store
            constraints = ConstraintSet()
            #make the ethereum world state
            world = evm.EVMWorld(constraints)

            address=0x222222222222222222222222222222222222200
            caller=origin=0x111111111111111111111111111111111111100
            price=0
            value=10000
            bytecode='\x16'
            data = 'AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA'
            header = { 'coinbase': 0,
                        'timestamp': 0,
                        'number': 0,
                        'difficulty': 0,
                        'gaslimit': 0,
                        }
            gas = 1000000

            new_vm = evm.EVM(constraints, address, origin, price, data, caller, value, bytecode, header, gas=gas, global_storage=world.storage)
            new_vm._push(57896044618658097711785492504343953926634992332820282019728792003956564819952L)
            new_vm._push(16)
            last_exception, last_returned = self._execute(new_vm)
            self.assertEqual(last_exception, None)
            self.assertEqual(new_vm.pc, 1)
            self.assertEqual(new_vm.stack, [16L])

    def test_AND_34(self):
            #Make the constraint store
            constraints = ConstraintSet()
            #make the ethereum world state
            world = evm.EVMWorld(constraints)

            address=0x222222222222222222222222222222222222200
            caller=origin=0x111111111111111111111111111111111111100
            price=0
            value=10000
            bytecode='\x16'
            data = 'AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA'
            header = { 'coinbase': 0,
                        'timestamp': 0,
                        'number': 0,
                        'difficulty': 0,
                        'gaslimit': 0,
                        }
            gas = 1000000

            new_vm = evm.EVM(constraints, address, origin, price, data, caller, value, bytecode, header, gas=gas, global_storage=world.storage)
            new_vm._push(57896044618658097711785492504343953926634992332820282019728792003956564819952L)
            new_vm._push(32)
            last_exception, last_returned = self._execute(new_vm)
            self.assertEqual(last_exception, None)
            self.assertEqual(new_vm.pc, 1)
            self.assertEqual(new_vm.stack, [32L])

    def test_AND_35(self):
            #Make the constraint store
            constraints = ConstraintSet()
            #make the ethereum world state
            world = evm.EVMWorld(constraints)

            address=0x222222222222222222222222222222222222200
            caller=origin=0x111111111111111111111111111111111111100
            price=0
            value=10000
            bytecode='\x16'
            data = 'AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA'
            header = { 'coinbase': 0,
                        'timestamp': 0,
                        'number': 0,
                        'difficulty': 0,
                        'gaslimit': 0,
                        }
            gas = 1000000

            new_vm = evm.EVM(constraints, address, origin, price, data, caller, value, bytecode, header, gas=gas, global_storage=world.storage)
            new_vm._push(57896044618658097711785492504343953926634992332820282019728792003956564819952L)
            new_vm._push(48)
            last_exception, last_returned = self._execute(new_vm)
            self.assertEqual(last_exception, None)
            self.assertEqual(new_vm.pc, 1)
            self.assertEqual(new_vm.stack, [48L])

    def test_AND_36(self):
            #Make the constraint store
            constraints = ConstraintSet()
            #make the ethereum world state
            world = evm.EVMWorld(constraints)

            address=0x222222222222222222222222222222222222200
            caller=origin=0x111111111111111111111111111111111111100
            price=0
            value=10000
            bytecode='\x16'
            data = 'AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA'
            header = { 'coinbase': 0,
                        'timestamp': 0,
                        'number': 0,
                        'difficulty': 0,
                        'gaslimit': 0,
                        }
            gas = 1000000

            new_vm = evm.EVM(constraints, address, origin, price, data, caller, value, bytecode, header, gas=gas, global_storage=world.storage)
            new_vm._push(57896044618658097711785492504343953926634992332820282019728792003956564819952L)
            new_vm._push(6089590155545428825848686802984512581899718912L)
            last_exception, last_returned = self._execute(new_vm)
            self.assertEqual(last_exception, None)
            self.assertEqual(new_vm.pc, 1)
            self.assertEqual(new_vm.stack, [6089590155545428825848686802984512581899718912L])

    def test_AND_37(self):
            #Make the constraint store
            constraints = ConstraintSet()
            #make the ethereum world state
            world = evm.EVMWorld(constraints)

            address=0x222222222222222222222222222222222222200
            caller=origin=0x111111111111111111111111111111111111100
            price=0
            value=10000
            bytecode='\x16'
            data = 'AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA'
            header = { 'coinbase': 0,
                        'timestamp': 0,
                        'number': 0,
                        'difficulty': 0,
                        'gaslimit': 0,
                        }
            gas = 1000000

            new_vm = evm.EVM(constraints, address, origin, price, data, caller, value, bytecode, header, gas=gas, global_storage=world.storage)
            new_vm._push(3618502788666131106986593281521497120414687020801267626233049500247285301263L)
            new_vm._push(115792089237316195423570985008687907853269984665640564039457584007913129639935L)
            last_exception, last_returned = self._execute(new_vm)
            self.assertEqual(last_exception, None)
            self.assertEqual(new_vm.pc, 1)
            self.assertEqual(new_vm.stack, [3618502788666131106986593281521497120414687020801267626233049500247285301263L])

    def test_AND_38(self):
            #Make the constraint store
            constraints = ConstraintSet()
            #make the ethereum world state
            world = evm.EVMWorld(constraints)

            address=0x222222222222222222222222222222222222200
            caller=origin=0x111111111111111111111111111111111111100
            price=0
            value=10000
            bytecode='\x16'
            data = 'AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA'
            header = { 'coinbase': 0,
                        'timestamp': 0,
                        'number': 0,
                        'difficulty': 0,
                        'gaslimit': 0,
                        }
            gas = 1000000

            new_vm = evm.EVM(constraints, address, origin, price, data, caller, value, bytecode, header, gas=gas, global_storage=world.storage)
            new_vm._push(3618502788666131106986593281521497120414687020801267626233049500247285301263L)
            new_vm._push(0)
            last_exception, last_returned = self._execute(new_vm)
            self.assertEqual(last_exception, None)
            self.assertEqual(new_vm.pc, 1)
            self.assertEqual(new_vm.stack, [0L])

    def test_AND_39(self):
            #Make the constraint store
            constraints = ConstraintSet()
            #make the ethereum world state
            world = evm.EVMWorld(constraints)

            address=0x222222222222222222222222222222222222200
            caller=origin=0x111111111111111111111111111111111111100
            price=0
            value=10000
            bytecode='\x16'
            data = 'AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA'
            header = { 'coinbase': 0,
                        'timestamp': 0,
                        'number': 0,
                        'difficulty': 0,
                        'gaslimit': 0,
                        }
            gas = 1000000

            new_vm = evm.EVM(constraints, address, origin, price, data, caller, value, bytecode, header, gas=gas, global_storage=world.storage)
            new_vm._push(3618502788666131106986593281521497120414687020801267626233049500247285301263L)
            new_vm._push(1)
            last_exception, last_returned = self._execute(new_vm)
            self.assertEqual(last_exception, None)
            self.assertEqual(new_vm.pc, 1)
            self.assertEqual(new_vm.stack, [1L])

    def test_AND_40(self):
            #Make the constraint store
            constraints = ConstraintSet()
            #make the ethereum world state
            world = evm.EVMWorld(constraints)

            address=0x222222222222222222222222222222222222200
            caller=origin=0x111111111111111111111111111111111111100
            price=0
            value=10000
            bytecode='\x16'
            data = 'AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA'
            header = { 'coinbase': 0,
                        'timestamp': 0,
                        'number': 0,
                        'difficulty': 0,
                        'gaslimit': 0,
                        }
            gas = 1000000

            new_vm = evm.EVM(constraints, address, origin, price, data, caller, value, bytecode, header, gas=gas, global_storage=world.storage)
            new_vm._push(3618502788666131106986593281521497120414687020801267626233049500247285301263L)
            new_vm._push(57896044618658097711785492504343953926634992332820282019728792003956564819952L)
            last_exception, last_returned = self._execute(new_vm)
            self.assertEqual(last_exception, None)
            self.assertEqual(new_vm.pc, 1)
            self.assertEqual(new_vm.stack, [3618502788666131106986593281521497120414687020801267626233049500247285301248L])

    def test_AND_41(self):
            #Make the constraint store
            constraints = ConstraintSet()
            #make the ethereum world state
            world = evm.EVMWorld(constraints)

            address=0x222222222222222222222222222222222222200
            caller=origin=0x111111111111111111111111111111111111100
            price=0
            value=10000
            bytecode='\x16'
            data = 'AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA'
            header = { 'coinbase': 0,
                        'timestamp': 0,
                        'number': 0,
                        'difficulty': 0,
                        'gaslimit': 0,
                        }
            gas = 1000000

            new_vm = evm.EVM(constraints, address, origin, price, data, caller, value, bytecode, header, gas=gas, global_storage=world.storage)
            new_vm._push(3618502788666131106986593281521497120414687020801267626233049500247285301263L)
            new_vm._push(3618502788666131106986593281521497120414687020801267626233049500247285301263L)
            last_exception, last_returned = self._execute(new_vm)
            self.assertEqual(last_exception, None)
            self.assertEqual(new_vm.pc, 1)
            self.assertEqual(new_vm.stack, [3618502788666131106986593281521497120414687020801267626233049500247285301263L])

    def test_AND_42(self):
            #Make the constraint store
            constraints = ConstraintSet()
            #make the ethereum world state
            world = evm.EVMWorld(constraints)

            address=0x222222222222222222222222222222222222200
            caller=origin=0x111111111111111111111111111111111111100
            price=0
            value=10000
            bytecode='\x16'
            data = 'AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA'
            header = { 'coinbase': 0,
                        'timestamp': 0,
                        'number': 0,
                        'difficulty': 0,
                        'gaslimit': 0,
                        }
            gas = 1000000

            new_vm = evm.EVM(constraints, address, origin, price, data, caller, value, bytecode, header, gas=gas, global_storage=world.storage)
            new_vm._push(3618502788666131106986593281521497120414687020801267626233049500247285301263L)
            new_vm._push(16)
            last_exception, last_returned = self._execute(new_vm)
            self.assertEqual(last_exception, None)
            self.assertEqual(new_vm.pc, 1)
            self.assertEqual(new_vm.stack, [0L])

    def test_AND_43(self):
            #Make the constraint store
            constraints = ConstraintSet()
            #make the ethereum world state
            world = evm.EVMWorld(constraints)

            address=0x222222222222222222222222222222222222200
            caller=origin=0x111111111111111111111111111111111111100
            price=0
            value=10000
            bytecode='\x16'
            data = 'AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA'
            header = { 'coinbase': 0,
                        'timestamp': 0,
                        'number': 0,
                        'difficulty': 0,
                        'gaslimit': 0,
                        }
            gas = 1000000

            new_vm = evm.EVM(constraints, address, origin, price, data, caller, value, bytecode, header, gas=gas, global_storage=world.storage)
            new_vm._push(3618502788666131106986593281521497120414687020801267626233049500247285301263L)
            new_vm._push(32)
            last_exception, last_returned = self._execute(new_vm)
            self.assertEqual(last_exception, None)
            self.assertEqual(new_vm.pc, 1)
            self.assertEqual(new_vm.stack, [0L])

    def test_AND_44(self):
            #Make the constraint store
            constraints = ConstraintSet()
            #make the ethereum world state
            world = evm.EVMWorld(constraints)

            address=0x222222222222222222222222222222222222200
            caller=origin=0x111111111111111111111111111111111111100
            price=0
            value=10000
            bytecode='\x16'
            data = 'AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA'
            header = { 'coinbase': 0,
                        'timestamp': 0,
                        'number': 0,
                        'difficulty': 0,
                        'gaslimit': 0,
                        }
            gas = 1000000

            new_vm = evm.EVM(constraints, address, origin, price, data, caller, value, bytecode, header, gas=gas, global_storage=world.storage)
            new_vm._push(3618502788666131106986593281521497120414687020801267626233049500247285301263L)
            new_vm._push(48)
            last_exception, last_returned = self._execute(new_vm)
            self.assertEqual(last_exception, None)
            self.assertEqual(new_vm.pc, 1)
            self.assertEqual(new_vm.stack, [0L])

    def test_AND_45(self):
            #Make the constraint store
            constraints = ConstraintSet()
            #make the ethereum world state
            world = evm.EVMWorld(constraints)

            address=0x222222222222222222222222222222222222200
            caller=origin=0x111111111111111111111111111111111111100
            price=0
            value=10000
            bytecode='\x16'
            data = 'AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA'
            header = { 'coinbase': 0,
                        'timestamp': 0,
                        'number': 0,
                        'difficulty': 0,
                        'gaslimit': 0,
                        }
            gas = 1000000

            new_vm = evm.EVM(constraints, address, origin, price, data, caller, value, bytecode, header, gas=gas, global_storage=world.storage)
            new_vm._push(3618502788666131106986593281521497120414687020801267626233049500247285301263L)
            new_vm._push(6089590155545428825848686802984512581899718912L)
            last_exception, last_returned = self._execute(new_vm)
            self.assertEqual(last_exception, None)
            self.assertEqual(new_vm.pc, 1)
            self.assertEqual(new_vm.stack, [0L])

    def test_AND_46(self):
            #Make the constraint store
            constraints = ConstraintSet()
            #make the ethereum world state
            world = evm.EVMWorld(constraints)

            address=0x222222222222222222222222222222222222200
            caller=origin=0x111111111111111111111111111111111111100
            price=0
            value=10000
            bytecode='\x16'
            data = 'AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA'
            header = { 'coinbase': 0,
                        'timestamp': 0,
                        'number': 0,
                        'difficulty': 0,
                        'gaslimit': 0,
                        }
            gas = 1000000

            new_vm = evm.EVM(constraints, address, origin, price, data, caller, value, bytecode, header, gas=gas, global_storage=world.storage)
            new_vm._push(16)
            new_vm._push(115792089237316195423570985008687907853269984665640564039457584007913129639935L)
            last_exception, last_returned = self._execute(new_vm)
            self.assertEqual(last_exception, None)
            self.assertEqual(new_vm.pc, 1)
            self.assertEqual(new_vm.stack, [16L])

    def test_AND_47(self):
            #Make the constraint store
            constraints = ConstraintSet()
            #make the ethereum world state
            world = evm.EVMWorld(constraints)

            address=0x222222222222222222222222222222222222200
            caller=origin=0x111111111111111111111111111111111111100
            price=0
            value=10000
            bytecode='\x16'
            data = 'AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA'
            header = { 'coinbase': 0,
                        'timestamp': 0,
                        'number': 0,
                        'difficulty': 0,
                        'gaslimit': 0,
                        }
            gas = 1000000

            new_vm = evm.EVM(constraints, address, origin, price, data, caller, value, bytecode, header, gas=gas, global_storage=world.storage)
            new_vm._push(16)
            new_vm._push(0)
            last_exception, last_returned = self._execute(new_vm)
            self.assertEqual(last_exception, None)
            self.assertEqual(new_vm.pc, 1)
            self.assertEqual(new_vm.stack, [0])

    def test_AND_48(self):
            #Make the constraint store
            constraints = ConstraintSet()
            #make the ethereum world state
            world = evm.EVMWorld(constraints)

            address=0x222222222222222222222222222222222222200
            caller=origin=0x111111111111111111111111111111111111100
            price=0
            value=10000
            bytecode='\x16'
            data = 'AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA'
            header = { 'coinbase': 0,
                        'timestamp': 0,
                        'number': 0,
                        'difficulty': 0,
                        'gaslimit': 0,
                        }
            gas = 1000000

            new_vm = evm.EVM(constraints, address, origin, price, data, caller, value, bytecode, header, gas=gas, global_storage=world.storage)
            new_vm._push(16)
            new_vm._push(1)
            last_exception, last_returned = self._execute(new_vm)
            self.assertEqual(last_exception, None)
            self.assertEqual(new_vm.pc, 1)
            self.assertEqual(new_vm.stack, [0])

    def test_AND_49(self):
            #Make the constraint store
            constraints = ConstraintSet()
            #make the ethereum world state
            world = evm.EVMWorld(constraints)

            address=0x222222222222222222222222222222222222200
            caller=origin=0x111111111111111111111111111111111111100
            price=0
            value=10000
            bytecode='\x16'
            data = 'AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA'
            header = { 'coinbase': 0,
                        'timestamp': 0,
                        'number': 0,
                        'difficulty': 0,
                        'gaslimit': 0,
                        }
            gas = 1000000

            new_vm = evm.EVM(constraints, address, origin, price, data, caller, value, bytecode, header, gas=gas, global_storage=world.storage)
            new_vm._push(16)
            new_vm._push(57896044618658097711785492504343953926634992332820282019728792003956564819952L)
            last_exception, last_returned = self._execute(new_vm)
            self.assertEqual(last_exception, None)
            self.assertEqual(new_vm.pc, 1)
            self.assertEqual(new_vm.stack, [16L])

    def test_AND_50(self):
            #Make the constraint store
            constraints = ConstraintSet()
            #make the ethereum world state
            world = evm.EVMWorld(constraints)

            address=0x222222222222222222222222222222222222200
            caller=origin=0x111111111111111111111111111111111111100
            price=0
            value=10000
            bytecode='\x16'
            data = 'AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA'
            header = { 'coinbase': 0,
                        'timestamp': 0,
                        'number': 0,
                        'difficulty': 0,
                        'gaslimit': 0,
                        }
            gas = 1000000

            new_vm = evm.EVM(constraints, address, origin, price, data, caller, value, bytecode, header, gas=gas, global_storage=world.storage)
            new_vm._push(16)
            new_vm._push(3618502788666131106986593281521497120414687020801267626233049500247285301263L)
            last_exception, last_returned = self._execute(new_vm)
            self.assertEqual(last_exception, None)
            self.assertEqual(new_vm.pc, 1)
            self.assertEqual(new_vm.stack, [0L])

    def test_AND_51(self):
            #Make the constraint store
            constraints = ConstraintSet()
            #make the ethereum world state
            world = evm.EVMWorld(constraints)

            address=0x222222222222222222222222222222222222200
            caller=origin=0x111111111111111111111111111111111111100
            price=0
            value=10000
            bytecode='\x16'
            data = 'AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA'
            header = { 'coinbase': 0,
                        'timestamp': 0,
                        'number': 0,
                        'difficulty': 0,
                        'gaslimit': 0,
                        }
            gas = 1000000

            new_vm = evm.EVM(constraints, address, origin, price, data, caller, value, bytecode, header, gas=gas, global_storage=world.storage)
            new_vm._push(16)
            new_vm._push(16)
            last_exception, last_returned = self._execute(new_vm)
            self.assertEqual(last_exception, None)
            self.assertEqual(new_vm.pc, 1)
            self.assertEqual(new_vm.stack, [16])

    def test_AND_52(self):
            #Make the constraint store
            constraints = ConstraintSet()
            #make the ethereum world state
            world = evm.EVMWorld(constraints)

            address=0x222222222222222222222222222222222222200
            caller=origin=0x111111111111111111111111111111111111100
            price=0
            value=10000
            bytecode='\x16'
            data = 'AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA'
            header = { 'coinbase': 0,
                        'timestamp': 0,
                        'number': 0,
                        'difficulty': 0,
                        'gaslimit': 0,
                        }
            gas = 1000000

            new_vm = evm.EVM(constraints, address, origin, price, data, caller, value, bytecode, header, gas=gas, global_storage=world.storage)
            new_vm._push(16)
            new_vm._push(32)
            last_exception, last_returned = self._execute(new_vm)
            self.assertEqual(last_exception, None)
            self.assertEqual(new_vm.pc, 1)
            self.assertEqual(new_vm.stack, [0])

    def test_AND_53(self):
            #Make the constraint store
            constraints = ConstraintSet()
            #make the ethereum world state
            world = evm.EVMWorld(constraints)

            address=0x222222222222222222222222222222222222200
            caller=origin=0x111111111111111111111111111111111111100
            price=0
            value=10000
            bytecode='\x16'
            data = 'AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA'
            header = { 'coinbase': 0,
                        'timestamp': 0,
                        'number': 0,
                        'difficulty': 0,
                        'gaslimit': 0,
                        }
            gas = 1000000

            new_vm = evm.EVM(constraints, address, origin, price, data, caller, value, bytecode, header, gas=gas, global_storage=world.storage)
            new_vm._push(16)
            new_vm._push(48)
            last_exception, last_returned = self._execute(new_vm)
            self.assertEqual(last_exception, None)
            self.assertEqual(new_vm.pc, 1)
            self.assertEqual(new_vm.stack, [16])

    def test_AND_54(self):
            #Make the constraint store
            constraints = ConstraintSet()
            #make the ethereum world state
            world = evm.EVMWorld(constraints)

            address=0x222222222222222222222222222222222222200
            caller=origin=0x111111111111111111111111111111111111100
            price=0
            value=10000
            bytecode='\x16'
            data = 'AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA'
            header = { 'coinbase': 0,
                        'timestamp': 0,
                        'number': 0,
                        'difficulty': 0,
                        'gaslimit': 0,
                        }
            gas = 1000000

            new_vm = evm.EVM(constraints, address, origin, price, data, caller, value, bytecode, header, gas=gas, global_storage=world.storage)
            new_vm._push(16)
            new_vm._push(6089590155545428825848686802984512581899718912L)
            last_exception, last_returned = self._execute(new_vm)
            self.assertEqual(last_exception, None)
            self.assertEqual(new_vm.pc, 1)
            self.assertEqual(new_vm.stack, [0L])

    def test_AND_55(self):
            #Make the constraint store
            constraints = ConstraintSet()
            #make the ethereum world state
            world = evm.EVMWorld(constraints)

            address=0x222222222222222222222222222222222222200
            caller=origin=0x111111111111111111111111111111111111100
            price=0
            value=10000
            bytecode='\x16'
            data = 'AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA'
            header = { 'coinbase': 0,
                        'timestamp': 0,
                        'number': 0,
                        'difficulty': 0,
                        'gaslimit': 0,
                        }
            gas = 1000000

            new_vm = evm.EVM(constraints, address, origin, price, data, caller, value, bytecode, header, gas=gas, global_storage=world.storage)
            new_vm._push(32)
            new_vm._push(115792089237316195423570985008687907853269984665640564039457584007913129639935L)
            last_exception, last_returned = self._execute(new_vm)
            self.assertEqual(last_exception, None)
            self.assertEqual(new_vm.pc, 1)
            self.assertEqual(new_vm.stack, [32L])

    def test_AND_56(self):
            #Make the constraint store
            constraints = ConstraintSet()
            #make the ethereum world state
            world = evm.EVMWorld(constraints)

            address=0x222222222222222222222222222222222222200
            caller=origin=0x111111111111111111111111111111111111100
            price=0
            value=10000
            bytecode='\x16'
            data = 'AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA'
            header = { 'coinbase': 0,
                        'timestamp': 0,
                        'number': 0,
                        'difficulty': 0,
                        'gaslimit': 0,
                        }
            gas = 1000000

            new_vm = evm.EVM(constraints, address, origin, price, data, caller, value, bytecode, header, gas=gas, global_storage=world.storage)
            new_vm._push(32)
            new_vm._push(0)
            last_exception, last_returned = self._execute(new_vm)
            self.assertEqual(last_exception, None)
            self.assertEqual(new_vm.pc, 1)
            self.assertEqual(new_vm.stack, [0])

    def test_AND_57(self):
            #Make the constraint store
            constraints = ConstraintSet()
            #make the ethereum world state
            world = evm.EVMWorld(constraints)

            address=0x222222222222222222222222222222222222200
            caller=origin=0x111111111111111111111111111111111111100
            price=0
            value=10000
            bytecode='\x16'
            data = 'AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA'
            header = { 'coinbase': 0,
                        'timestamp': 0,
                        'number': 0,
                        'difficulty': 0,
                        'gaslimit': 0,
                        }
            gas = 1000000

            new_vm = evm.EVM(constraints, address, origin, price, data, caller, value, bytecode, header, gas=gas, global_storage=world.storage)
            new_vm._push(32)
            new_vm._push(1)
            last_exception, last_returned = self._execute(new_vm)
            self.assertEqual(last_exception, None)
            self.assertEqual(new_vm.pc, 1)
            self.assertEqual(new_vm.stack, [0])

    def test_AND_58(self):
            #Make the constraint store
            constraints = ConstraintSet()
            #make the ethereum world state
            world = evm.EVMWorld(constraints)

            address=0x222222222222222222222222222222222222200
            caller=origin=0x111111111111111111111111111111111111100
            price=0
            value=10000
            bytecode='\x16'
            data = 'AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA'
            header = { 'coinbase': 0,
                        'timestamp': 0,
                        'number': 0,
                        'difficulty': 0,
                        'gaslimit': 0,
                        }
            gas = 1000000

            new_vm = evm.EVM(constraints, address, origin, price, data, caller, value, bytecode, header, gas=gas, global_storage=world.storage)
            new_vm._push(32)
            new_vm._push(57896044618658097711785492504343953926634992332820282019728792003956564819952L)
            last_exception, last_returned = self._execute(new_vm)
            self.assertEqual(last_exception, None)
            self.assertEqual(new_vm.pc, 1)
            self.assertEqual(new_vm.stack, [32L])

    def test_AND_59(self):
            #Make the constraint store
            constraints = ConstraintSet()
            #make the ethereum world state
            world = evm.EVMWorld(constraints)

            address=0x222222222222222222222222222222222222200
            caller=origin=0x111111111111111111111111111111111111100
            price=0
            value=10000
            bytecode='\x16'
            data = 'AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA'
            header = { 'coinbase': 0,
                        'timestamp': 0,
                        'number': 0,
                        'difficulty': 0,
                        'gaslimit': 0,
                        }
            gas = 1000000

            new_vm = evm.EVM(constraints, address, origin, price, data, caller, value, bytecode, header, gas=gas, global_storage=world.storage)
            new_vm._push(32)
            new_vm._push(3618502788666131106986593281521497120414687020801267626233049500247285301263L)
            last_exception, last_returned = self._execute(new_vm)
            self.assertEqual(last_exception, None)
            self.assertEqual(new_vm.pc, 1)
            self.assertEqual(new_vm.stack, [0L])

    def test_AND_60(self):
            #Make the constraint store
            constraints = ConstraintSet()
            #make the ethereum world state
            world = evm.EVMWorld(constraints)

            address=0x222222222222222222222222222222222222200
            caller=origin=0x111111111111111111111111111111111111100
            price=0
            value=10000
            bytecode='\x16'
            data = 'AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA'
            header = { 'coinbase': 0,
                        'timestamp': 0,
                        'number': 0,
                        'difficulty': 0,
                        'gaslimit': 0,
                        }
            gas = 1000000

            new_vm = evm.EVM(constraints, address, origin, price, data, caller, value, bytecode, header, gas=gas, global_storage=world.storage)
            new_vm._push(32)
            new_vm._push(16)
            last_exception, last_returned = self._execute(new_vm)
            self.assertEqual(last_exception, None)
            self.assertEqual(new_vm.pc, 1)
            self.assertEqual(new_vm.stack, [0])

    def test_AND_61(self):
            #Make the constraint store
            constraints = ConstraintSet()
            #make the ethereum world state
            world = evm.EVMWorld(constraints)

            address=0x222222222222222222222222222222222222200
            caller=origin=0x111111111111111111111111111111111111100
            price=0
            value=10000
            bytecode='\x16'
            data = 'AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA'
            header = { 'coinbase': 0,
                        'timestamp': 0,
                        'number': 0,
                        'difficulty': 0,
                        'gaslimit': 0,
                        }
            gas = 1000000

            new_vm = evm.EVM(constraints, address, origin, price, data, caller, value, bytecode, header, gas=gas, global_storage=world.storage)
            new_vm._push(32)
            new_vm._push(32)
            last_exception, last_returned = self._execute(new_vm)
            self.assertEqual(last_exception, None)
            self.assertEqual(new_vm.pc, 1)
            self.assertEqual(new_vm.stack, [32])

    def test_AND_62(self):
            #Make the constraint store
            constraints = ConstraintSet()
            #make the ethereum world state
            world = evm.EVMWorld(constraints)

            address=0x222222222222222222222222222222222222200
            caller=origin=0x111111111111111111111111111111111111100
            price=0
            value=10000
            bytecode='\x16'
            data = 'AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA'
            header = { 'coinbase': 0,
                        'timestamp': 0,
                        'number': 0,
                        'difficulty': 0,
                        'gaslimit': 0,
                        }
            gas = 1000000

            new_vm = evm.EVM(constraints, address, origin, price, data, caller, value, bytecode, header, gas=gas, global_storage=world.storage)
            new_vm._push(32)
            new_vm._push(48)
            last_exception, last_returned = self._execute(new_vm)
            self.assertEqual(last_exception, None)
            self.assertEqual(new_vm.pc, 1)
            self.assertEqual(new_vm.stack, [32])

    def test_AND_63(self):
            #Make the constraint store
            constraints = ConstraintSet()
            #make the ethereum world state
            world = evm.EVMWorld(constraints)

            address=0x222222222222222222222222222222222222200
            caller=origin=0x111111111111111111111111111111111111100
            price=0
            value=10000
            bytecode='\x16'
            data = 'AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA'
            header = { 'coinbase': 0,
                        'timestamp': 0,
                        'number': 0,
                        'difficulty': 0,
                        'gaslimit': 0,
                        }
            gas = 1000000

            new_vm = evm.EVM(constraints, address, origin, price, data, caller, value, bytecode, header, gas=gas, global_storage=world.storage)
            new_vm._push(32)
            new_vm._push(6089590155545428825848686802984512581899718912L)
            last_exception, last_returned = self._execute(new_vm)
            self.assertEqual(last_exception, None)
            self.assertEqual(new_vm.pc, 1)
            self.assertEqual(new_vm.stack, [0L])

    def test_AND_64(self):
            #Make the constraint store
            constraints = ConstraintSet()
            #make the ethereum world state
            world = evm.EVMWorld(constraints)

            address=0x222222222222222222222222222222222222200
            caller=origin=0x111111111111111111111111111111111111100
            price=0
            value=10000
            bytecode='\x16'
            data = 'AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA'
            header = { 'coinbase': 0,
                        'timestamp': 0,
                        'number': 0,
                        'difficulty': 0,
                        'gaslimit': 0,
                        }
            gas = 1000000

            new_vm = evm.EVM(constraints, address, origin, price, data, caller, value, bytecode, header, gas=gas, global_storage=world.storage)
            new_vm._push(48)
            new_vm._push(115792089237316195423570985008687907853269984665640564039457584007913129639935L)
            last_exception, last_returned = self._execute(new_vm)
            self.assertEqual(last_exception, None)
            self.assertEqual(new_vm.pc, 1)
            self.assertEqual(new_vm.stack, [48L])

    def test_AND_65(self):
            #Make the constraint store
            constraints = ConstraintSet()
            #make the ethereum world state
            world = evm.EVMWorld(constraints)

            address=0x222222222222222222222222222222222222200
            caller=origin=0x111111111111111111111111111111111111100
            price=0
            value=10000
            bytecode='\x16'
            data = 'AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA'
            header = { 'coinbase': 0,
                        'timestamp': 0,
                        'number': 0,
                        'difficulty': 0,
                        'gaslimit': 0,
                        }
            gas = 1000000

            new_vm = evm.EVM(constraints, address, origin, price, data, caller, value, bytecode, header, gas=gas, global_storage=world.storage)
            new_vm._push(48)
            new_vm._push(0)
            last_exception, last_returned = self._execute(new_vm)
            self.assertEqual(last_exception, None)
            self.assertEqual(new_vm.pc, 1)
            self.assertEqual(new_vm.stack, [0])

    def test_AND_66(self):
            #Make the constraint store
            constraints = ConstraintSet()
            #make the ethereum world state
            world = evm.EVMWorld(constraints)

            address=0x222222222222222222222222222222222222200
            caller=origin=0x111111111111111111111111111111111111100
            price=0
            value=10000
            bytecode='\x16'
            data = 'AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA'
            header = { 'coinbase': 0,
                        'timestamp': 0,
                        'number': 0,
                        'difficulty': 0,
                        'gaslimit': 0,
                        }
            gas = 1000000

            new_vm = evm.EVM(constraints, address, origin, price, data, caller, value, bytecode, header, gas=gas, global_storage=world.storage)
            new_vm._push(48)
            new_vm._push(1)
            last_exception, last_returned = self._execute(new_vm)
            self.assertEqual(last_exception, None)
            self.assertEqual(new_vm.pc, 1)
            self.assertEqual(new_vm.stack, [0])

    def test_AND_67(self):
            #Make the constraint store
            constraints = ConstraintSet()
            #make the ethereum world state
            world = evm.EVMWorld(constraints)

            address=0x222222222222222222222222222222222222200
            caller=origin=0x111111111111111111111111111111111111100
            price=0
            value=10000
            bytecode='\x16'
            data = 'AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA'
            header = { 'coinbase': 0,
                        'timestamp': 0,
                        'number': 0,
                        'difficulty': 0,
                        'gaslimit': 0,
                        }
            gas = 1000000

            new_vm = evm.EVM(constraints, address, origin, price, data, caller, value, bytecode, header, gas=gas, global_storage=world.storage)
            new_vm._push(48)
            new_vm._push(57896044618658097711785492504343953926634992332820282019728792003956564819952L)
            last_exception, last_returned = self._execute(new_vm)
            self.assertEqual(last_exception, None)
            self.assertEqual(new_vm.pc, 1)
            self.assertEqual(new_vm.stack, [48L])

    def test_AND_68(self):
            #Make the constraint store
            constraints = ConstraintSet()
            #make the ethereum world state
            world = evm.EVMWorld(constraints)

            address=0x222222222222222222222222222222222222200
            caller=origin=0x111111111111111111111111111111111111100
            price=0
            value=10000
            bytecode='\x16'
            data = 'AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA'
            header = { 'coinbase': 0,
                        'timestamp': 0,
                        'number': 0,
                        'difficulty': 0,
                        'gaslimit': 0,
                        }
            gas = 1000000

            new_vm = evm.EVM(constraints, address, origin, price, data, caller, value, bytecode, header, gas=gas, global_storage=world.storage)
            new_vm._push(48)
            new_vm._push(3618502788666131106986593281521497120414687020801267626233049500247285301263L)
            last_exception, last_returned = self._execute(new_vm)
            self.assertEqual(last_exception, None)
            self.assertEqual(new_vm.pc, 1)
            self.assertEqual(new_vm.stack, [0L])

    def test_AND_69(self):
            #Make the constraint store
            constraints = ConstraintSet()
            #make the ethereum world state
            world = evm.EVMWorld(constraints)

            address=0x222222222222222222222222222222222222200
            caller=origin=0x111111111111111111111111111111111111100
            price=0
            value=10000
            bytecode='\x16'
            data = 'AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA'
            header = { 'coinbase': 0,
                        'timestamp': 0,
                        'number': 0,
                        'difficulty': 0,
                        'gaslimit': 0,
                        }
            gas = 1000000

            new_vm = evm.EVM(constraints, address, origin, price, data, caller, value, bytecode, header, gas=gas, global_storage=world.storage)
            new_vm._push(48)
            new_vm._push(16)
            last_exception, last_returned = self._execute(new_vm)
            self.assertEqual(last_exception, None)
            self.assertEqual(new_vm.pc, 1)
            self.assertEqual(new_vm.stack, [16])

    def test_AND_70(self):
            #Make the constraint store
            constraints = ConstraintSet()
            #make the ethereum world state
            world = evm.EVMWorld(constraints)

            address=0x222222222222222222222222222222222222200
            caller=origin=0x111111111111111111111111111111111111100
            price=0
            value=10000
            bytecode='\x16'
            data = 'AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA'
            header = { 'coinbase': 0,
                        'timestamp': 0,
                        'number': 0,
                        'difficulty': 0,
                        'gaslimit': 0,
                        }
            gas = 1000000

            new_vm = evm.EVM(constraints, address, origin, price, data, caller, value, bytecode, header, gas=gas, global_storage=world.storage)
            new_vm._push(48)
            new_vm._push(32)
            last_exception, last_returned = self._execute(new_vm)
            self.assertEqual(last_exception, None)
            self.assertEqual(new_vm.pc, 1)
            self.assertEqual(new_vm.stack, [32])

    def test_AND_71(self):
            #Make the constraint store
            constraints = ConstraintSet()
            #make the ethereum world state
            world = evm.EVMWorld(constraints)

            address=0x222222222222222222222222222222222222200
            caller=origin=0x111111111111111111111111111111111111100
            price=0
            value=10000
            bytecode='\x16'
            data = 'AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA'
            header = { 'coinbase': 0,
                        'timestamp': 0,
                        'number': 0,
                        'difficulty': 0,
                        'gaslimit': 0,
                        }
            gas = 1000000

            new_vm = evm.EVM(constraints, address, origin, price, data, caller, value, bytecode, header, gas=gas, global_storage=world.storage)
            new_vm._push(48)
            new_vm._push(48)
            last_exception, last_returned = self._execute(new_vm)
            self.assertEqual(last_exception, None)
            self.assertEqual(new_vm.pc, 1)
            self.assertEqual(new_vm.stack, [48])

    def test_AND_72(self):
            #Make the constraint store
            constraints = ConstraintSet()
            #make the ethereum world state
            world = evm.EVMWorld(constraints)

            address=0x222222222222222222222222222222222222200
            caller=origin=0x111111111111111111111111111111111111100
            price=0
            value=10000
            bytecode='\x16'
            data = 'AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA'
            header = { 'coinbase': 0,
                        'timestamp': 0,
                        'number': 0,
                        'difficulty': 0,
                        'gaslimit': 0,
                        }
            gas = 1000000

            new_vm = evm.EVM(constraints, address, origin, price, data, caller, value, bytecode, header, gas=gas, global_storage=world.storage)
            new_vm._push(48)
            new_vm._push(6089590155545428825848686802984512581899718912L)
            last_exception, last_returned = self._execute(new_vm)
            self.assertEqual(last_exception, None)
            self.assertEqual(new_vm.pc, 1)
            self.assertEqual(new_vm.stack, [0L])

    def test_AND_73(self):
            #Make the constraint store
            constraints = ConstraintSet()
            #make the ethereum world state
            world = evm.EVMWorld(constraints)

            address=0x222222222222222222222222222222222222200
            caller=origin=0x111111111111111111111111111111111111100
            price=0
            value=10000
            bytecode='\x16'
            data = 'AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA'
            header = { 'coinbase': 0,
                        'timestamp': 0,
                        'number': 0,
                        'difficulty': 0,
                        'gaslimit': 0,
                        }
            gas = 1000000

            new_vm = evm.EVM(constraints, address, origin, price, data, caller, value, bytecode, header, gas=gas, global_storage=world.storage)
            new_vm._push(6089590155545428825848686802984512581899718912L)
            new_vm._push(115792089237316195423570985008687907853269984665640564039457584007913129639935L)
            last_exception, last_returned = self._execute(new_vm)
            self.assertEqual(last_exception, None)
            self.assertEqual(new_vm.pc, 1)
            self.assertEqual(new_vm.stack, [6089590155545428825848686802984512581899718912L])

    def test_AND_74(self):
            #Make the constraint store
            constraints = ConstraintSet()
            #make the ethereum world state
            world = evm.EVMWorld(constraints)

            address=0x222222222222222222222222222222222222200
            caller=origin=0x111111111111111111111111111111111111100
            price=0
            value=10000
            bytecode='\x16'
            data = 'AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA'
            header = { 'coinbase': 0,
                        'timestamp': 0,
                        'number': 0,
                        'difficulty': 0,
                        'gaslimit': 0,
                        }
            gas = 1000000

            new_vm = evm.EVM(constraints, address, origin, price, data, caller, value, bytecode, header, gas=gas, global_storage=world.storage)
            new_vm._push(6089590155545428825848686802984512581899718912L)
            new_vm._push(0)
            last_exception, last_returned = self._execute(new_vm)
            self.assertEqual(last_exception, None)
            self.assertEqual(new_vm.pc, 1)
            self.assertEqual(new_vm.stack, [0L])

    def test_AND_75(self):
            #Make the constraint store
            constraints = ConstraintSet()
            #make the ethereum world state
            world = evm.EVMWorld(constraints)

            address=0x222222222222222222222222222222222222200
            caller=origin=0x111111111111111111111111111111111111100
            price=0
            value=10000
            bytecode='\x16'
            data = 'AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA'
            header = { 'coinbase': 0,
                        'timestamp': 0,
                        'number': 0,
                        'difficulty': 0,
                        'gaslimit': 0,
                        }
            gas = 1000000

            new_vm = evm.EVM(constraints, address, origin, price, data, caller, value, bytecode, header, gas=gas, global_storage=world.storage)
            new_vm._push(6089590155545428825848686802984512581899718912L)
            new_vm._push(1)
            last_exception, last_returned = self._execute(new_vm)
            self.assertEqual(last_exception, None)
            self.assertEqual(new_vm.pc, 1)
            self.assertEqual(new_vm.stack, [0L])

    def test_AND_76(self):
            #Make the constraint store
            constraints = ConstraintSet()
            #make the ethereum world state
            world = evm.EVMWorld(constraints)

            address=0x222222222222222222222222222222222222200
            caller=origin=0x111111111111111111111111111111111111100
            price=0
            value=10000
            bytecode='\x16'
            data = 'AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA'
            header = { 'coinbase': 0,
                        'timestamp': 0,
                        'number': 0,
                        'difficulty': 0,
                        'gaslimit': 0,
                        }
            gas = 1000000

            new_vm = evm.EVM(constraints, address, origin, price, data, caller, value, bytecode, header, gas=gas, global_storage=world.storage)
            new_vm._push(6089590155545428825848686802984512581899718912L)
            new_vm._push(57896044618658097711785492504343953926634992332820282019728792003956564819952L)
            last_exception, last_returned = self._execute(new_vm)
            self.assertEqual(last_exception, None)
            self.assertEqual(new_vm.pc, 1)
            self.assertEqual(new_vm.stack, [6089590155545428825848686802984512581899718912L])

    def test_AND_77(self):
            #Make the constraint store
            constraints = ConstraintSet()
            #make the ethereum world state
            world = evm.EVMWorld(constraints)

            address=0x222222222222222222222222222222222222200
            caller=origin=0x111111111111111111111111111111111111100
            price=0
            value=10000
            bytecode='\x16'
            data = 'AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA'
            header = { 'coinbase': 0,
                        'timestamp': 0,
                        'number': 0,
                        'difficulty': 0,
                        'gaslimit': 0,
                        }
            gas = 1000000

            new_vm = evm.EVM(constraints, address, origin, price, data, caller, value, bytecode, header, gas=gas, global_storage=world.storage)
            new_vm._push(6089590155545428825848686802984512581899718912L)
            new_vm._push(3618502788666131106986593281521497120414687020801267626233049500247285301263L)
            last_exception, last_returned = self._execute(new_vm)
            self.assertEqual(last_exception, None)
            self.assertEqual(new_vm.pc, 1)
            self.assertEqual(new_vm.stack, [0L])

    def test_AND_78(self):
            #Make the constraint store
            constraints = ConstraintSet()
            #make the ethereum world state
            world = evm.EVMWorld(constraints)

            address=0x222222222222222222222222222222222222200
            caller=origin=0x111111111111111111111111111111111111100
            price=0
            value=10000
            bytecode='\x16'
            data = 'AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA'
            header = { 'coinbase': 0,
                        'timestamp': 0,
                        'number': 0,
                        'difficulty': 0,
                        'gaslimit': 0,
                        }
            gas = 1000000

            new_vm = evm.EVM(constraints, address, origin, price, data, caller, value, bytecode, header, gas=gas, global_storage=world.storage)
            new_vm._push(6089590155545428825848686802984512581899718912L)
            new_vm._push(16)
            last_exception, last_returned = self._execute(new_vm)
            self.assertEqual(last_exception, None)
            self.assertEqual(new_vm.pc, 1)
            self.assertEqual(new_vm.stack, [0L])

    def test_AND_79(self):
            #Make the constraint store
            constraints = ConstraintSet()
            #make the ethereum world state
            world = evm.EVMWorld(constraints)

            address=0x222222222222222222222222222222222222200
            caller=origin=0x111111111111111111111111111111111111100
            price=0
            value=10000
            bytecode='\x16'
            data = 'AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA'
            header = { 'coinbase': 0,
                        'timestamp': 0,
                        'number': 0,
                        'difficulty': 0,
                        'gaslimit': 0,
                        }
            gas = 1000000

            new_vm = evm.EVM(constraints, address, origin, price, data, caller, value, bytecode, header, gas=gas, global_storage=world.storage)
            new_vm._push(6089590155545428825848686802984512581899718912L)
            new_vm._push(32)
            last_exception, last_returned = self._execute(new_vm)
            self.assertEqual(last_exception, None)
            self.assertEqual(new_vm.pc, 1)
            self.assertEqual(new_vm.stack, [0L])

    def test_AND_80(self):
            #Make the constraint store
            constraints = ConstraintSet()
            #make the ethereum world state
            world = evm.EVMWorld(constraints)

            address=0x222222222222222222222222222222222222200
            caller=origin=0x111111111111111111111111111111111111100
            price=0
            value=10000
            bytecode='\x16'
            data = 'AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA'
            header = { 'coinbase': 0,
                        'timestamp': 0,
                        'number': 0,
                        'difficulty': 0,
                        'gaslimit': 0,
                        }
            gas = 1000000

            new_vm = evm.EVM(constraints, address, origin, price, data, caller, value, bytecode, header, gas=gas, global_storage=world.storage)
            new_vm._push(6089590155545428825848686802984512581899718912L)
            new_vm._push(48)
            last_exception, last_returned = self._execute(new_vm)
            self.assertEqual(last_exception, None)
            self.assertEqual(new_vm.pc, 1)
            self.assertEqual(new_vm.stack, [0L])

    def test_AND_81(self):
            #Make the constraint store
            constraints = ConstraintSet()
            #make the ethereum world state
            world = evm.EVMWorld(constraints)

            address=0x222222222222222222222222222222222222200
            caller=origin=0x111111111111111111111111111111111111100
            price=0
            value=10000
            bytecode='\x16'
            data = 'AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA'
            header = { 'coinbase': 0,
                        'timestamp': 0,
                        'number': 0,
                        'difficulty': 0,
                        'gaslimit': 0,
                        }
            gas = 1000000

            new_vm = evm.EVM(constraints, address, origin, price, data, caller, value, bytecode, header, gas=gas, global_storage=world.storage)
            new_vm._push(6089590155545428825848686802984512581899718912L)
            new_vm._push(6089590155545428825848686802984512581899718912L)
            last_exception, last_returned = self._execute(new_vm)
            self.assertEqual(last_exception, None)
            self.assertEqual(new_vm.pc, 1)
            self.assertEqual(new_vm.stack, [6089590155545428825848686802984512581899718912L])

if __name__ == '__main__':
    unittest.main()
