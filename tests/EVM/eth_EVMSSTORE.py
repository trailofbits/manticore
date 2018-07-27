
import struct
import unittest
import json
from manticore.platforms import evm
from manticore.core import state
from manticore.core.smtlib import Operators, ConstraintSet
import os


class EVMTest_SSTORE(unittest.TestCase):
    _multiprocess_can_split_ = True
    maxDiff=None 
    def _execute(self, new_vm):
        last_returned = None
        last_exception = None
        try:
            new_vm.execute()
        except evm.Stop as e:
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

    def test_SSTORE_1(self):
            #Make the constraint store
            constraints = ConstraintSet()
            #make the ethereum world state
            world = evm.EVMWorld(constraints)

            address = 0x222222222222222222222222222222222222200
            balance = None
            code = 'U'
            storage = {115792089237316195423570985008687907853269984665640564039457584007913129639935: 115792089237316195423570985008687907853269984665640564039457584007913129639935}
            world.create_account( address=address, balance=balance, code=code, storage=storage)

            address=0x222222222222222222222222222222222222200
            caller=origin=0x111111111111111111111111111111111111100
            price=0
            value=10000
            bytecode='U'
            data = 'AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA'
            header = { 'coinbase': 0,
                        'timestamp': 0,
                        'number': 0,
                        'difficulty': 0,
                        'gaslimit': 0,
                        }
            gas = 1000000

            new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, gas=gas, world=world)
            new_vm._push(115792089237316195423570985008687907853269984665640564039457584007913129639935)
            new_vm._push(115792089237316195423570985008687907853269984665640564039457584007913129639935)
            last_exception, last_returned = self._execute(new_vm)
            self.assertEqual(last_exception, None)
            self.assertEqual(new_vm.pc, 1)
            self.assertEqual(new_vm.stack, [])

    def test_SSTORE_2(self):
            #Make the constraint store
            constraints = ConstraintSet()
            #make the ethereum world state
            world = evm.EVMWorld(constraints)

            address = 0x222222222222222222222222222222222222200
            balance = None
            code = 'U'
            storage = {0: 115792089237316195423570985008687907853269984665640564039457584007913129639935}
            world.create_account( address=address, balance=balance, code=code, storage=storage)

            address=0x222222222222222222222222222222222222200
            caller=origin=0x111111111111111111111111111111111111100
            price=0
            value=10000
            bytecode='U'
            data = 'AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA'
            header = { 'coinbase': 0,
                        'timestamp': 0,
                        'number': 0,
                        'difficulty': 0,
                        'gaslimit': 0,
                        }
            gas = 1000000

            new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, gas=gas, world=world)
            new_vm._push(115792089237316195423570985008687907853269984665640564039457584007913129639935)
            new_vm._push(0)
            last_exception, last_returned = self._execute(new_vm)
            self.assertEqual(last_exception, None)
            self.assertEqual(new_vm.pc, 1)
            self.assertEqual(new_vm.stack, [])

    def test_SSTORE_3(self):
            #Make the constraint store
            constraints = ConstraintSet()
            #make the ethereum world state
            world = evm.EVMWorld(constraints)

            address = 0x222222222222222222222222222222222222200
            balance = None
            code = 'U'
            storage = {1: 115792089237316195423570985008687907853269984665640564039457584007913129639935}
            world.create_account( address=address, balance=balance, code=code, storage=storage)

            address=0x222222222222222222222222222222222222200
            caller=origin=0x111111111111111111111111111111111111100
            price=0
            value=10000
            bytecode='U'
            data = 'AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA'
            header = { 'coinbase': 0,
                        'timestamp': 0,
                        'number': 0,
                        'difficulty': 0,
                        'gaslimit': 0,
                        }
            gas = 1000000

            new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, gas=gas, world=world)
            new_vm._push(115792089237316195423570985008687907853269984665640564039457584007913129639935)
            new_vm._push(1)
            last_exception, last_returned = self._execute(new_vm)
            self.assertEqual(last_exception, None)
            self.assertEqual(new_vm.pc, 1)
            self.assertEqual(new_vm.stack, [])

    def test_SSTORE_4(self):
            #Make the constraint store
            constraints = ConstraintSet()
            #make the ethereum world state
            world = evm.EVMWorld(constraints)

            address = 0x222222222222222222222222222222222222200
            balance = None
            code = 'U'
            storage = {57896044618658097711785492504343953926634992332820282019728792003956564819952: 115792089237316195423570985008687907853269984665640564039457584007913129639935}
            world.create_account( address=address, balance=balance, code=code, storage=storage)

            address=0x222222222222222222222222222222222222200
            caller=origin=0x111111111111111111111111111111111111100
            price=0
            value=10000
            bytecode='U'
            data = 'AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA'
            header = { 'coinbase': 0,
                        'timestamp': 0,
                        'number': 0,
                        'difficulty': 0,
                        'gaslimit': 0,
                        }
            gas = 1000000

            new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, gas=gas, world=world)
            new_vm._push(115792089237316195423570985008687907853269984665640564039457584007913129639935)
            new_vm._push(57896044618658097711785492504343953926634992332820282019728792003956564819952)
            last_exception, last_returned = self._execute(new_vm)
            self.assertEqual(last_exception, None)
            self.assertEqual(new_vm.pc, 1)
            self.assertEqual(new_vm.stack, [])

    def test_SSTORE_5(self):
            #Make the constraint store
            constraints = ConstraintSet()
            #make the ethereum world state
            world = evm.EVMWorld(constraints)

            address = 0x222222222222222222222222222222222222200
            balance = None
            code = 'U'
            storage = {3618502788666131106986593281521497120414687020801267626233049500247285301263: 115792089237316195423570985008687907853269984665640564039457584007913129639935}
            world.create_account( address=address, balance=balance, code=code, storage=storage)

            address=0x222222222222222222222222222222222222200
            caller=origin=0x111111111111111111111111111111111111100
            price=0
            value=10000
            bytecode='U'
            data = 'AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA'
            header = { 'coinbase': 0,
                        'timestamp': 0,
                        'number': 0,
                        'difficulty': 0,
                        'gaslimit': 0,
                        }
            gas = 1000000

            new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, gas=gas, world=world)
            new_vm._push(115792089237316195423570985008687907853269984665640564039457584007913129639935)
            new_vm._push(3618502788666131106986593281521497120414687020801267626233049500247285301263)
            last_exception, last_returned = self._execute(new_vm)
            self.assertEqual(last_exception, None)
            self.assertEqual(new_vm.pc, 1)
            self.assertEqual(new_vm.stack, [])

    def test_SSTORE_6(self):
            #Make the constraint store
            constraints = ConstraintSet()
            #make the ethereum world state
            world = evm.EVMWorld(constraints)

            address = 0x222222222222222222222222222222222222200
            balance = None
            code = 'U'
            storage = {16: 115792089237316195423570985008687907853269984665640564039457584007913129639935}
            world.create_account( address=address, balance=balance, code=code, storage=storage)

            address=0x222222222222222222222222222222222222200
            caller=origin=0x111111111111111111111111111111111111100
            price=0
            value=10000
            bytecode='U'
            data = 'AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA'
            header = { 'coinbase': 0,
                        'timestamp': 0,
                        'number': 0,
                        'difficulty': 0,
                        'gaslimit': 0,
                        }
            gas = 1000000

            new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, gas=gas, world=world)
            new_vm._push(115792089237316195423570985008687907853269984665640564039457584007913129639935)
            new_vm._push(16)
            last_exception, last_returned = self._execute(new_vm)
            self.assertEqual(last_exception, None)
            self.assertEqual(new_vm.pc, 1)
            self.assertEqual(new_vm.stack, [])

    def test_SSTORE_7(self):
            #Make the constraint store
            constraints = ConstraintSet()
            #make the ethereum world state
            world = evm.EVMWorld(constraints)

            address = 0x222222222222222222222222222222222222200
            balance = None
            code = 'U'
            storage = {32: 115792089237316195423570985008687907853269984665640564039457584007913129639935}
            world.create_account( address=address, balance=balance, code=code, storage=storage)

            address=0x222222222222222222222222222222222222200
            caller=origin=0x111111111111111111111111111111111111100
            price=0
            value=10000
            bytecode='U'
            data = 'AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA'
            header = { 'coinbase': 0,
                        'timestamp': 0,
                        'number': 0,
                        'difficulty': 0,
                        'gaslimit': 0,
                        }
            gas = 1000000

            new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, gas=gas, world=world)
            new_vm._push(115792089237316195423570985008687907853269984665640564039457584007913129639935)
            new_vm._push(32)
            last_exception, last_returned = self._execute(new_vm)
            self.assertEqual(last_exception, None)
            self.assertEqual(new_vm.pc, 1)
            self.assertEqual(new_vm.stack, [])

    def test_SSTORE_8(self):
            #Make the constraint store
            constraints = ConstraintSet()
            #make the ethereum world state
            world = evm.EVMWorld(constraints)

            address = 0x222222222222222222222222222222222222200
            balance = None
            code = 'U'
            storage = {48: 115792089237316195423570985008687907853269984665640564039457584007913129639935}
            world.create_account( address=address, balance=balance, code=code, storage=storage)

            address=0x222222222222222222222222222222222222200
            caller=origin=0x111111111111111111111111111111111111100
            price=0
            value=10000
            bytecode='U'
            data = 'AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA'
            header = { 'coinbase': 0,
                        'timestamp': 0,
                        'number': 0,
                        'difficulty': 0,
                        'gaslimit': 0,
                        }
            gas = 1000000

            new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, gas=gas, world=world)
            new_vm._push(115792089237316195423570985008687907853269984665640564039457584007913129639935)
            new_vm._push(48)
            last_exception, last_returned = self._execute(new_vm)
            self.assertEqual(last_exception, None)
            self.assertEqual(new_vm.pc, 1)
            self.assertEqual(new_vm.stack, [])

    def test_SSTORE_9(self):
            #Make the constraint store
            constraints = ConstraintSet()
            #make the ethereum world state
            world = evm.EVMWorld(constraints)

            address = 0x222222222222222222222222222222222222200
            balance = None
            code = 'U'
            storage = {6089590155545428825848686802984512581899718912: 115792089237316195423570985008687907853269984665640564039457584007913129639935}
            world.create_account( address=address, balance=balance, code=code, storage=storage)

            address=0x222222222222222222222222222222222222200
            caller=origin=0x111111111111111111111111111111111111100
            price=0
            value=10000
            bytecode='U'
            data = 'AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA'
            header = { 'coinbase': 0,
                        'timestamp': 0,
                        'number': 0,
                        'difficulty': 0,
                        'gaslimit': 0,
                        }
            gas = 1000000

            new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, gas=gas, world=world)
            new_vm._push(115792089237316195423570985008687907853269984665640564039457584007913129639935)
            new_vm._push(6089590155545428825848686802984512581899718912)
            last_exception, last_returned = self._execute(new_vm)
            self.assertEqual(last_exception, None)
            self.assertEqual(new_vm.pc, 1)
            self.assertEqual(new_vm.stack, [])

    def test_SSTORE_10(self):
            #Make the constraint store
            constraints = ConstraintSet()
            #make the ethereum world state
            world = evm.EVMWorld(constraints)

            address = 0x222222222222222222222222222222222222200
            balance = None
            code = 'U'
            storage = {115792089237316195423570985008687907853269984665640564039457584007913129639935: 0}
            world.create_account( address=address, balance=balance, code=code, storage=storage)

            address=0x222222222222222222222222222222222222200
            caller=origin=0x111111111111111111111111111111111111100
            price=0
            value=10000
            bytecode='U'
            data = 'AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA'
            header = { 'coinbase': 0,
                        'timestamp': 0,
                        'number': 0,
                        'difficulty': 0,
                        'gaslimit': 0,
                        }
            gas = 1000000

            new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, gas=gas, world=world)
            new_vm._push(0)
            new_vm._push(115792089237316195423570985008687907853269984665640564039457584007913129639935)
            last_exception, last_returned = self._execute(new_vm)
            self.assertEqual(last_exception, None)
            self.assertEqual(new_vm.pc, 1)
            self.assertEqual(new_vm.stack, [])

    def test_SSTORE_11(self):
            #Make the constraint store
            constraints = ConstraintSet()
            #make the ethereum world state
            world = evm.EVMWorld(constraints)

            address = 0x222222222222222222222222222222222222200
            balance = None
            code = 'U'
            storage = {0: 0}
            world.create_account( address=address, balance=balance, code=code, storage=storage)

            address=0x222222222222222222222222222222222222200
            caller=origin=0x111111111111111111111111111111111111100
            price=0
            value=10000
            bytecode='U'
            data = 'AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA'
            header = { 'coinbase': 0,
                        'timestamp': 0,
                        'number': 0,
                        'difficulty': 0,
                        'gaslimit': 0,
                        }
            gas = 1000000

            new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, gas=gas, world=world)
            new_vm._push(0)
            new_vm._push(0)
            last_exception, last_returned = self._execute(new_vm)
            self.assertEqual(last_exception, None)
            self.assertEqual(new_vm.pc, 1)
            self.assertEqual(new_vm.stack, [])

    def test_SSTORE_12(self):
            #Make the constraint store
            constraints = ConstraintSet()
            #make the ethereum world state
            world = evm.EVMWorld(constraints)

            address = 0x222222222222222222222222222222222222200
            balance = None
            code = 'U'
            storage = {1: 0}
            world.create_account( address=address, balance=balance, code=code, storage=storage)

            address=0x222222222222222222222222222222222222200
            caller=origin=0x111111111111111111111111111111111111100
            price=0
            value=10000
            bytecode='U'
            data = 'AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA'
            header = { 'coinbase': 0,
                        'timestamp': 0,
                        'number': 0,
                        'difficulty': 0,
                        'gaslimit': 0,
                        }
            gas = 1000000

            new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, gas=gas, world=world)
            new_vm._push(0)
            new_vm._push(1)
            last_exception, last_returned = self._execute(new_vm)
            self.assertEqual(last_exception, None)
            self.assertEqual(new_vm.pc, 1)
            self.assertEqual(new_vm.stack, [])

    def test_SSTORE_13(self):
            #Make the constraint store
            constraints = ConstraintSet()
            #make the ethereum world state
            world = evm.EVMWorld(constraints)

            address = 0x222222222222222222222222222222222222200
            balance = None
            code = 'U'
            storage = {57896044618658097711785492504343953926634992332820282019728792003956564819952: 0}
            world.create_account( address=address, balance=balance, code=code, storage=storage)

            address=0x222222222222222222222222222222222222200
            caller=origin=0x111111111111111111111111111111111111100
            price=0
            value=10000
            bytecode='U'
            data = 'AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA'
            header = { 'coinbase': 0,
                        'timestamp': 0,
                        'number': 0,
                        'difficulty': 0,
                        'gaslimit': 0,
                        }
            gas = 1000000

            new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, gas=gas, world=world)
            new_vm._push(0)
            new_vm._push(57896044618658097711785492504343953926634992332820282019728792003956564819952)
            last_exception, last_returned = self._execute(new_vm)
            self.assertEqual(last_exception, None)
            self.assertEqual(new_vm.pc, 1)
            self.assertEqual(new_vm.stack, [])

    def test_SSTORE_14(self):
            #Make the constraint store
            constraints = ConstraintSet()
            #make the ethereum world state
            world = evm.EVMWorld(constraints)

            address = 0x222222222222222222222222222222222222200
            balance = None
            code = 'U'
            storage = {3618502788666131106986593281521497120414687020801267626233049500247285301263: 0}
            world.create_account( address=address, balance=balance, code=code, storage=storage)

            address=0x222222222222222222222222222222222222200
            caller=origin=0x111111111111111111111111111111111111100
            price=0
            value=10000
            bytecode='U'
            data = 'AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA'
            header = { 'coinbase': 0,
                        'timestamp': 0,
                        'number': 0,
                        'difficulty': 0,
                        'gaslimit': 0,
                        }
            gas = 1000000

            new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, gas=gas, world=world)
            new_vm._push(0)
            new_vm._push(3618502788666131106986593281521497120414687020801267626233049500247285301263)
            last_exception, last_returned = self._execute(new_vm)
            self.assertEqual(last_exception, None)
            self.assertEqual(new_vm.pc, 1)
            self.assertEqual(new_vm.stack, [])

    def test_SSTORE_15(self):
            #Make the constraint store
            constraints = ConstraintSet()
            #make the ethereum world state
            world = evm.EVMWorld(constraints)

            address = 0x222222222222222222222222222222222222200
            balance = None
            code = 'U'
            storage = {16: 0}
            world.create_account( address=address, balance=balance, code=code, storage=storage)

            address=0x222222222222222222222222222222222222200
            caller=origin=0x111111111111111111111111111111111111100
            price=0
            value=10000
            bytecode='U'
            data = 'AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA'
            header = { 'coinbase': 0,
                        'timestamp': 0,
                        'number': 0,
                        'difficulty': 0,
                        'gaslimit': 0,
                        }
            gas = 1000000

            new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, gas=gas, world=world)
            new_vm._push(0)
            new_vm._push(16)
            last_exception, last_returned = self._execute(new_vm)
            self.assertEqual(last_exception, None)
            self.assertEqual(new_vm.pc, 1)
            self.assertEqual(new_vm.stack, [])

    def test_SSTORE_16(self):
            #Make the constraint store
            constraints = ConstraintSet()
            #make the ethereum world state
            world = evm.EVMWorld(constraints)

            address = 0x222222222222222222222222222222222222200
            balance = None
            code = 'U'
            storage = {32: 0}
            world.create_account( address=address, balance=balance, code=code, storage=storage)

            address=0x222222222222222222222222222222222222200
            caller=origin=0x111111111111111111111111111111111111100
            price=0
            value=10000
            bytecode='U'
            data = 'AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA'
            header = { 'coinbase': 0,
                        'timestamp': 0,
                        'number': 0,
                        'difficulty': 0,
                        'gaslimit': 0,
                        }
            gas = 1000000

            new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, gas=gas, world=world)
            new_vm._push(0)
            new_vm._push(32)
            last_exception, last_returned = self._execute(new_vm)
            self.assertEqual(last_exception, None)
            self.assertEqual(new_vm.pc, 1)
            self.assertEqual(new_vm.stack, [])

    def test_SSTORE_17(self):
            #Make the constraint store
            constraints = ConstraintSet()
            #make the ethereum world state
            world = evm.EVMWorld(constraints)

            address = 0x222222222222222222222222222222222222200
            balance = None
            code = 'U'
            storage = {48: 0}
            world.create_account( address=address, balance=balance, code=code, storage=storage)

            address=0x222222222222222222222222222222222222200
            caller=origin=0x111111111111111111111111111111111111100
            price=0
            value=10000
            bytecode='U'
            data = 'AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA'
            header = { 'coinbase': 0,
                        'timestamp': 0,
                        'number': 0,
                        'difficulty': 0,
                        'gaslimit': 0,
                        }
            gas = 1000000

            new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, gas=gas, world=world)
            new_vm._push(0)
            new_vm._push(48)
            last_exception, last_returned = self._execute(new_vm)
            self.assertEqual(last_exception, None)
            self.assertEqual(new_vm.pc, 1)
            self.assertEqual(new_vm.stack, [])

    def test_SSTORE_18(self):
            #Make the constraint store
            constraints = ConstraintSet()
            #make the ethereum world state
            world = evm.EVMWorld(constraints)

            address = 0x222222222222222222222222222222222222200
            balance = None
            code = 'U'
            storage = {6089590155545428825848686802984512581899718912: 0}
            world.create_account( address=address, balance=balance, code=code, storage=storage)

            address=0x222222222222222222222222222222222222200
            caller=origin=0x111111111111111111111111111111111111100
            price=0
            value=10000
            bytecode='U'
            data = 'AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA'
            header = { 'coinbase': 0,
                        'timestamp': 0,
                        'number': 0,
                        'difficulty': 0,
                        'gaslimit': 0,
                        }
            gas = 1000000

            new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, gas=gas, world=world)
            new_vm._push(0)
            new_vm._push(6089590155545428825848686802984512581899718912)
            last_exception, last_returned = self._execute(new_vm)
            self.assertEqual(last_exception, None)
            self.assertEqual(new_vm.pc, 1)
            self.assertEqual(new_vm.stack, [])

    def test_SSTORE_19(self):
            #Make the constraint store
            constraints = ConstraintSet()
            #make the ethereum world state
            world = evm.EVMWorld(constraints)

            address = 0x222222222222222222222222222222222222200
            balance = None
            code = 'U'
            storage = {115792089237316195423570985008687907853269984665640564039457584007913129639935: 1}
            world.create_account( address=address, balance=balance, code=code, storage=storage)

            address=0x222222222222222222222222222222222222200
            caller=origin=0x111111111111111111111111111111111111100
            price=0
            value=10000
            bytecode='U'
            data = 'AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA'
            header = { 'coinbase': 0,
                        'timestamp': 0,
                        'number': 0,
                        'difficulty': 0,
                        'gaslimit': 0,
                        }
            gas = 1000000

            new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, gas=gas, world=world)
            new_vm._push(1)
            new_vm._push(115792089237316195423570985008687907853269984665640564039457584007913129639935)
            last_exception, last_returned = self._execute(new_vm)
            self.assertEqual(last_exception, None)
            self.assertEqual(new_vm.pc, 1)
            self.assertEqual(new_vm.stack, [])

    def test_SSTORE_20(self):
            #Make the constraint store
            constraints = ConstraintSet()
            #make the ethereum world state
            world = evm.EVMWorld(constraints)

            address = 0x222222222222222222222222222222222222200
            balance = None
            code = 'U'
            storage = {0: 1}
            world.create_account( address=address, balance=balance, code=code, storage=storage)

            address=0x222222222222222222222222222222222222200
            caller=origin=0x111111111111111111111111111111111111100
            price=0
            value=10000
            bytecode='U'
            data = 'AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA'
            header = { 'coinbase': 0,
                        'timestamp': 0,
                        'number': 0,
                        'difficulty': 0,
                        'gaslimit': 0,
                        }
            gas = 1000000

            new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, gas=gas, world=world)
            new_vm._push(1)
            new_vm._push(0)
            last_exception, last_returned = self._execute(new_vm)
            self.assertEqual(last_exception, None)
            self.assertEqual(new_vm.pc, 1)
            self.assertEqual(new_vm.stack, [])

    def test_SSTORE_21(self):
            #Make the constraint store
            constraints = ConstraintSet()
            #make the ethereum world state
            world = evm.EVMWorld(constraints)

            address = 0x222222222222222222222222222222222222200
            balance = None
            code = 'U'
            storage = {1: 1}
            world.create_account( address=address, balance=balance, code=code, storage=storage)

            address=0x222222222222222222222222222222222222200
            caller=origin=0x111111111111111111111111111111111111100
            price=0
            value=10000
            bytecode='U'
            data = 'AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA'
            header = { 'coinbase': 0,
                        'timestamp': 0,
                        'number': 0,
                        'difficulty': 0,
                        'gaslimit': 0,
                        }
            gas = 1000000

            new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, gas=gas, world=world)
            new_vm._push(1)
            new_vm._push(1)
            last_exception, last_returned = self._execute(new_vm)
            self.assertEqual(last_exception, None)
            self.assertEqual(new_vm.pc, 1)
            self.assertEqual(new_vm.stack, [])

    def test_SSTORE_22(self):
            #Make the constraint store
            constraints = ConstraintSet()
            #make the ethereum world state
            world = evm.EVMWorld(constraints)

            address = 0x222222222222222222222222222222222222200
            balance = None
            code = 'U'
            storage = {57896044618658097711785492504343953926634992332820282019728792003956564819952: 1}
            world.create_account( address=address, balance=balance, code=code, storage=storage)

            address=0x222222222222222222222222222222222222200
            caller=origin=0x111111111111111111111111111111111111100
            price=0
            value=10000
            bytecode='U'
            data = 'AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA'
            header = { 'coinbase': 0,
                        'timestamp': 0,
                        'number': 0,
                        'difficulty': 0,
                        'gaslimit': 0,
                        }
            gas = 1000000

            new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, gas=gas, world=world)
            new_vm._push(1)
            new_vm._push(57896044618658097711785492504343953926634992332820282019728792003956564819952)
            last_exception, last_returned = self._execute(new_vm)
            self.assertEqual(last_exception, None)
            self.assertEqual(new_vm.pc, 1)
            self.assertEqual(new_vm.stack, [])

    def test_SSTORE_23(self):
            #Make the constraint store
            constraints = ConstraintSet()
            #make the ethereum world state
            world = evm.EVMWorld(constraints)

            address = 0x222222222222222222222222222222222222200
            balance = None
            code = 'U'
            storage = {3618502788666131106986593281521497120414687020801267626233049500247285301263: 1}
            world.create_account( address=address, balance=balance, code=code, storage=storage)

            address=0x222222222222222222222222222222222222200
            caller=origin=0x111111111111111111111111111111111111100
            price=0
            value=10000
            bytecode='U'
            data = 'AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA'
            header = { 'coinbase': 0,
                        'timestamp': 0,
                        'number': 0,
                        'difficulty': 0,
                        'gaslimit': 0,
                        }
            gas = 1000000

            new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, gas=gas, world=world)
            new_vm._push(1)
            new_vm._push(3618502788666131106986593281521497120414687020801267626233049500247285301263)
            last_exception, last_returned = self._execute(new_vm)
            self.assertEqual(last_exception, None)
            self.assertEqual(new_vm.pc, 1)
            self.assertEqual(new_vm.stack, [])

    def test_SSTORE_24(self):
            #Make the constraint store
            constraints = ConstraintSet()
            #make the ethereum world state
            world = evm.EVMWorld(constraints)

            address = 0x222222222222222222222222222222222222200
            balance = None
            code = 'U'
            storage = {16: 1}
            world.create_account( address=address, balance=balance, code=code, storage=storage)

            address=0x222222222222222222222222222222222222200
            caller=origin=0x111111111111111111111111111111111111100
            price=0
            value=10000
            bytecode='U'
            data = 'AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA'
            header = { 'coinbase': 0,
                        'timestamp': 0,
                        'number': 0,
                        'difficulty': 0,
                        'gaslimit': 0,
                        }
            gas = 1000000

            new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, gas=gas, world=world)
            new_vm._push(1)
            new_vm._push(16)
            last_exception, last_returned = self._execute(new_vm)
            self.assertEqual(last_exception, None)
            self.assertEqual(new_vm.pc, 1)
            self.assertEqual(new_vm.stack, [])

    def test_SSTORE_25(self):
            #Make the constraint store
            constraints = ConstraintSet()
            #make the ethereum world state
            world = evm.EVMWorld(constraints)

            address = 0x222222222222222222222222222222222222200
            balance = None
            code = 'U'
            storage = {32: 1}
            world.create_account( address=address, balance=balance, code=code, storage=storage)

            address=0x222222222222222222222222222222222222200
            caller=origin=0x111111111111111111111111111111111111100
            price=0
            value=10000
            bytecode='U'
            data = 'AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA'
            header = { 'coinbase': 0,
                        'timestamp': 0,
                        'number': 0,
                        'difficulty': 0,
                        'gaslimit': 0,
                        }
            gas = 1000000

            new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, gas=gas, world=world)
            new_vm._push(1)
            new_vm._push(32)
            last_exception, last_returned = self._execute(new_vm)
            self.assertEqual(last_exception, None)
            self.assertEqual(new_vm.pc, 1)
            self.assertEqual(new_vm.stack, [])

    def test_SSTORE_26(self):
            #Make the constraint store
            constraints = ConstraintSet()
            #make the ethereum world state
            world = evm.EVMWorld(constraints)

            address = 0x222222222222222222222222222222222222200
            balance = None
            code = 'U'
            storage = {48: 1}
            world.create_account( address=address, balance=balance, code=code, storage=storage)

            address=0x222222222222222222222222222222222222200
            caller=origin=0x111111111111111111111111111111111111100
            price=0
            value=10000
            bytecode='U'
            data = 'AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA'
            header = { 'coinbase': 0,
                        'timestamp': 0,
                        'number': 0,
                        'difficulty': 0,
                        'gaslimit': 0,
                        }
            gas = 1000000

            new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, gas=gas, world=world)
            new_vm._push(1)
            new_vm._push(48)
            last_exception, last_returned = self._execute(new_vm)
            self.assertEqual(last_exception, None)
            self.assertEqual(new_vm.pc, 1)
            self.assertEqual(new_vm.stack, [])

    def test_SSTORE_27(self):
            #Make the constraint store
            constraints = ConstraintSet()
            #make the ethereum world state
            world = evm.EVMWorld(constraints)

            address = 0x222222222222222222222222222222222222200
            balance = None
            code = 'U'
            storage = {6089590155545428825848686802984512581899718912: 1}
            world.create_account( address=address, balance=balance, code=code, storage=storage)

            address=0x222222222222222222222222222222222222200
            caller=origin=0x111111111111111111111111111111111111100
            price=0
            value=10000
            bytecode='U'
            data = 'AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA'
            header = { 'coinbase': 0,
                        'timestamp': 0,
                        'number': 0,
                        'difficulty': 0,
                        'gaslimit': 0,
                        }
            gas = 1000000

            new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, gas=gas, world=world)
            new_vm._push(1)
            new_vm._push(6089590155545428825848686802984512581899718912)
            last_exception, last_returned = self._execute(new_vm)
            self.assertEqual(last_exception, None)
            self.assertEqual(new_vm.pc, 1)
            self.assertEqual(new_vm.stack, [])

    def test_SSTORE_28(self):
            #Make the constraint store
            constraints = ConstraintSet()
            #make the ethereum world state
            world = evm.EVMWorld(constraints)

            address = 0x222222222222222222222222222222222222200
            balance = None
            code = 'U'
            storage = {115792089237316195423570985008687907853269984665640564039457584007913129639935: 57896044618658097711785492504343953926634992332820282019728792003956564819952}
            world.create_account( address=address, balance=balance, code=code, storage=storage)

            address=0x222222222222222222222222222222222222200
            caller=origin=0x111111111111111111111111111111111111100
            price=0
            value=10000
            bytecode='U'
            data = 'AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA'
            header = { 'coinbase': 0,
                        'timestamp': 0,
                        'number': 0,
                        'difficulty': 0,
                        'gaslimit': 0,
                        }
            gas = 1000000

            new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, gas=gas, world=world)
            new_vm._push(57896044618658097711785492504343953926634992332820282019728792003956564819952)
            new_vm._push(115792089237316195423570985008687907853269984665640564039457584007913129639935)
            last_exception, last_returned = self._execute(new_vm)
            self.assertEqual(last_exception, None)
            self.assertEqual(new_vm.pc, 1)
            self.assertEqual(new_vm.stack, [])

    def test_SSTORE_29(self):
            #Make the constraint store
            constraints = ConstraintSet()
            #make the ethereum world state
            world = evm.EVMWorld(constraints)

            address = 0x222222222222222222222222222222222222200
            balance = None
            code = 'U'
            storage = {0: 57896044618658097711785492504343953926634992332820282019728792003956564819952}
            world.create_account( address=address, balance=balance, code=code, storage=storage)

            address=0x222222222222222222222222222222222222200
            caller=origin=0x111111111111111111111111111111111111100
            price=0
            value=10000
            bytecode='U'
            data = 'AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA'
            header = { 'coinbase': 0,
                        'timestamp': 0,
                        'number': 0,
                        'difficulty': 0,
                        'gaslimit': 0,
                        }
            gas = 1000000

            new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, gas=gas, world=world)
            new_vm._push(57896044618658097711785492504343953926634992332820282019728792003956564819952)
            new_vm._push(0)
            last_exception, last_returned = self._execute(new_vm)
            self.assertEqual(last_exception, None)
            self.assertEqual(new_vm.pc, 1)
            self.assertEqual(new_vm.stack, [])

    def test_SSTORE_30(self):
            #Make the constraint store
            constraints = ConstraintSet()
            #make the ethereum world state
            world = evm.EVMWorld(constraints)

            address = 0x222222222222222222222222222222222222200
            balance = None
            code = 'U'
            storage = {1: 57896044618658097711785492504343953926634992332820282019728792003956564819952}
            world.create_account( address=address, balance=balance, code=code, storage=storage)

            address=0x222222222222222222222222222222222222200
            caller=origin=0x111111111111111111111111111111111111100
            price=0
            value=10000
            bytecode='U'
            data = 'AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA'
            header = { 'coinbase': 0,
                        'timestamp': 0,
                        'number': 0,
                        'difficulty': 0,
                        'gaslimit': 0,
                        }
            gas = 1000000

            new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, gas=gas, world=world)
            new_vm._push(57896044618658097711785492504343953926634992332820282019728792003956564819952)
            new_vm._push(1)
            last_exception, last_returned = self._execute(new_vm)
            self.assertEqual(last_exception, None)
            self.assertEqual(new_vm.pc, 1)
            self.assertEqual(new_vm.stack, [])

    def test_SSTORE_31(self):
            #Make the constraint store
            constraints = ConstraintSet()
            #make the ethereum world state
            world = evm.EVMWorld(constraints)

            address = 0x222222222222222222222222222222222222200
            balance = None
            code = 'U'
            storage = {57896044618658097711785492504343953926634992332820282019728792003956564819952: 57896044618658097711785492504343953926634992332820282019728792003956564819952}
            world.create_account( address=address, balance=balance, code=code, storage=storage)

            address=0x222222222222222222222222222222222222200
            caller=origin=0x111111111111111111111111111111111111100
            price=0
            value=10000
            bytecode='U'
            data = 'AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA'
            header = { 'coinbase': 0,
                        'timestamp': 0,
                        'number': 0,
                        'difficulty': 0,
                        'gaslimit': 0,
                        }
            gas = 1000000

            new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, gas=gas, world=world)
            new_vm._push(57896044618658097711785492504343953926634992332820282019728792003956564819952)
            new_vm._push(57896044618658097711785492504343953926634992332820282019728792003956564819952)
            last_exception, last_returned = self._execute(new_vm)
            self.assertEqual(last_exception, None)
            self.assertEqual(new_vm.pc, 1)
            self.assertEqual(new_vm.stack, [])

    def test_SSTORE_32(self):
            #Make the constraint store
            constraints = ConstraintSet()
            #make the ethereum world state
            world = evm.EVMWorld(constraints)

            address = 0x222222222222222222222222222222222222200
            balance = None
            code = 'U'
            storage = {3618502788666131106986593281521497120414687020801267626233049500247285301263: 57896044618658097711785492504343953926634992332820282019728792003956564819952}
            world.create_account( address=address, balance=balance, code=code, storage=storage)

            address=0x222222222222222222222222222222222222200
            caller=origin=0x111111111111111111111111111111111111100
            price=0
            value=10000
            bytecode='U'
            data = 'AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA'
            header = { 'coinbase': 0,
                        'timestamp': 0,
                        'number': 0,
                        'difficulty': 0,
                        'gaslimit': 0,
                        }
            gas = 1000000

            new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, gas=gas, world=world)
            new_vm._push(57896044618658097711785492504343953926634992332820282019728792003956564819952)
            new_vm._push(3618502788666131106986593281521497120414687020801267626233049500247285301263)
            last_exception, last_returned = self._execute(new_vm)
            self.assertEqual(last_exception, None)
            self.assertEqual(new_vm.pc, 1)
            self.assertEqual(new_vm.stack, [])

    def test_SSTORE_33(self):
            #Make the constraint store
            constraints = ConstraintSet()
            #make the ethereum world state
            world = evm.EVMWorld(constraints)

            address = 0x222222222222222222222222222222222222200
            balance = None
            code = 'U'
            storage = {16: 57896044618658097711785492504343953926634992332820282019728792003956564819952}
            world.create_account( address=address, balance=balance, code=code, storage=storage)

            address=0x222222222222222222222222222222222222200
            caller=origin=0x111111111111111111111111111111111111100
            price=0
            value=10000
            bytecode='U'
            data = 'AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA'
            header = { 'coinbase': 0,
                        'timestamp': 0,
                        'number': 0,
                        'difficulty': 0,
                        'gaslimit': 0,
                        }
            gas = 1000000

            new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, gas=gas, world=world)
            new_vm._push(57896044618658097711785492504343953926634992332820282019728792003956564819952)
            new_vm._push(16)
            last_exception, last_returned = self._execute(new_vm)
            self.assertEqual(last_exception, None)
            self.assertEqual(new_vm.pc, 1)
            self.assertEqual(new_vm.stack, [])

    def test_SSTORE_34(self):
            #Make the constraint store
            constraints = ConstraintSet()
            #make the ethereum world state
            world = evm.EVMWorld(constraints)

            address = 0x222222222222222222222222222222222222200
            balance = None
            code = 'U'
            storage = {32: 57896044618658097711785492504343953926634992332820282019728792003956564819952}
            world.create_account( address=address, balance=balance, code=code, storage=storage)

            address=0x222222222222222222222222222222222222200
            caller=origin=0x111111111111111111111111111111111111100
            price=0
            value=10000
            bytecode='U'
            data = 'AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA'
            header = { 'coinbase': 0,
                        'timestamp': 0,
                        'number': 0,
                        'difficulty': 0,
                        'gaslimit': 0,
                        }
            gas = 1000000

            new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, gas=gas, world=world)
            new_vm._push(57896044618658097711785492504343953926634992332820282019728792003956564819952)
            new_vm._push(32)
            last_exception, last_returned = self._execute(new_vm)
            self.assertEqual(last_exception, None)
            self.assertEqual(new_vm.pc, 1)
            self.assertEqual(new_vm.stack, [])

    def test_SSTORE_35(self):
            #Make the constraint store
            constraints = ConstraintSet()
            #make the ethereum world state
            world = evm.EVMWorld(constraints)

            address = 0x222222222222222222222222222222222222200
            balance = None
            code = 'U'
            storage = {48: 57896044618658097711785492504343953926634992332820282019728792003956564819952}
            world.create_account( address=address, balance=balance, code=code, storage=storage)

            address=0x222222222222222222222222222222222222200
            caller=origin=0x111111111111111111111111111111111111100
            price=0
            value=10000
            bytecode='U'
            data = 'AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA'
            header = { 'coinbase': 0,
                        'timestamp': 0,
                        'number': 0,
                        'difficulty': 0,
                        'gaslimit': 0,
                        }
            gas = 1000000

            new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, gas=gas, world=world)
            new_vm._push(57896044618658097711785492504343953926634992332820282019728792003956564819952)
            new_vm._push(48)
            last_exception, last_returned = self._execute(new_vm)
            self.assertEqual(last_exception, None)
            self.assertEqual(new_vm.pc, 1)
            self.assertEqual(new_vm.stack, [])

    def test_SSTORE_36(self):
            #Make the constraint store
            constraints = ConstraintSet()
            #make the ethereum world state
            world = evm.EVMWorld(constraints)

            address = 0x222222222222222222222222222222222222200
            balance = None
            code = 'U'
            storage = {6089590155545428825848686802984512581899718912: 57896044618658097711785492504343953926634992332820282019728792003956564819952}
            world.create_account( address=address, balance=balance, code=code, storage=storage)

            address=0x222222222222222222222222222222222222200
            caller=origin=0x111111111111111111111111111111111111100
            price=0
            value=10000
            bytecode='U'
            data = 'AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA'
            header = { 'coinbase': 0,
                        'timestamp': 0,
                        'number': 0,
                        'difficulty': 0,
                        'gaslimit': 0,
                        }
            gas = 1000000

            new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, gas=gas, world=world)
            new_vm._push(57896044618658097711785492504343953926634992332820282019728792003956564819952)
            new_vm._push(6089590155545428825848686802984512581899718912)
            last_exception, last_returned = self._execute(new_vm)
            self.assertEqual(last_exception, None)
            self.assertEqual(new_vm.pc, 1)
            self.assertEqual(new_vm.stack, [])

    def test_SSTORE_37(self):
            #Make the constraint store
            constraints = ConstraintSet()
            #make the ethereum world state
            world = evm.EVMWorld(constraints)

            address = 0x222222222222222222222222222222222222200
            balance = None
            code = 'U'
            storage = {115792089237316195423570985008687907853269984665640564039457584007913129639935: 3618502788666131106986593281521497120414687020801267626233049500247285301263}
            world.create_account( address=address, balance=balance, code=code, storage=storage)

            address=0x222222222222222222222222222222222222200
            caller=origin=0x111111111111111111111111111111111111100
            price=0
            value=10000
            bytecode='U'
            data = 'AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA'
            header = { 'coinbase': 0,
                        'timestamp': 0,
                        'number': 0,
                        'difficulty': 0,
                        'gaslimit': 0,
                        }
            gas = 1000000

            new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, gas=gas, world=world)
            new_vm._push(3618502788666131106986593281521497120414687020801267626233049500247285301263)
            new_vm._push(115792089237316195423570985008687907853269984665640564039457584007913129639935)
            last_exception, last_returned = self._execute(new_vm)
            self.assertEqual(last_exception, None)
            self.assertEqual(new_vm.pc, 1)
            self.assertEqual(new_vm.stack, [])

    def test_SSTORE_38(self):
            #Make the constraint store
            constraints = ConstraintSet()
            #make the ethereum world state
            world = evm.EVMWorld(constraints)

            address = 0x222222222222222222222222222222222222200
            balance = None
            code = 'U'
            storage = {0: 3618502788666131106986593281521497120414687020801267626233049500247285301263}
            world.create_account( address=address, balance=balance, code=code, storage=storage)

            address=0x222222222222222222222222222222222222200
            caller=origin=0x111111111111111111111111111111111111100
            price=0
            value=10000
            bytecode='U'
            data = 'AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA'
            header = { 'coinbase': 0,
                        'timestamp': 0,
                        'number': 0,
                        'difficulty': 0,
                        'gaslimit': 0,
                        }
            gas = 1000000

            new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, gas=gas, world=world)
            new_vm._push(3618502788666131106986593281521497120414687020801267626233049500247285301263)
            new_vm._push(0)
            last_exception, last_returned = self._execute(new_vm)
            self.assertEqual(last_exception, None)
            self.assertEqual(new_vm.pc, 1)
            self.assertEqual(new_vm.stack, [])

    def test_SSTORE_39(self):
            #Make the constraint store
            constraints = ConstraintSet()
            #make the ethereum world state
            world = evm.EVMWorld(constraints)

            address = 0x222222222222222222222222222222222222200
            balance = None
            code = 'U'
            storage = {1: 3618502788666131106986593281521497120414687020801267626233049500247285301263}
            world.create_account( address=address, balance=balance, code=code, storage=storage)

            address=0x222222222222222222222222222222222222200
            caller=origin=0x111111111111111111111111111111111111100
            price=0
            value=10000
            bytecode='U'
            data = 'AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA'
            header = { 'coinbase': 0,
                        'timestamp': 0,
                        'number': 0,
                        'difficulty': 0,
                        'gaslimit': 0,
                        }
            gas = 1000000

            new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, gas=gas, world=world)
            new_vm._push(3618502788666131106986593281521497120414687020801267626233049500247285301263)
            new_vm._push(1)
            last_exception, last_returned = self._execute(new_vm)
            self.assertEqual(last_exception, None)
            self.assertEqual(new_vm.pc, 1)
            self.assertEqual(new_vm.stack, [])

    def test_SSTORE_40(self):
            #Make the constraint store
            constraints = ConstraintSet()
            #make the ethereum world state
            world = evm.EVMWorld(constraints)

            address = 0x222222222222222222222222222222222222200
            balance = None
            code = 'U'
            storage = {57896044618658097711785492504343953926634992332820282019728792003956564819952: 3618502788666131106986593281521497120414687020801267626233049500247285301263}
            world.create_account( address=address, balance=balance, code=code, storage=storage)

            address=0x222222222222222222222222222222222222200
            caller=origin=0x111111111111111111111111111111111111100
            price=0
            value=10000
            bytecode='U'
            data = 'AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA'
            header = { 'coinbase': 0,
                        'timestamp': 0,
                        'number': 0,
                        'difficulty': 0,
                        'gaslimit': 0,
                        }
            gas = 1000000

            new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, gas=gas, world=world)
            new_vm._push(3618502788666131106986593281521497120414687020801267626233049500247285301263)
            new_vm._push(57896044618658097711785492504343953926634992332820282019728792003956564819952)
            last_exception, last_returned = self._execute(new_vm)
            self.assertEqual(last_exception, None)
            self.assertEqual(new_vm.pc, 1)
            self.assertEqual(new_vm.stack, [])

    def test_SSTORE_41(self):
            #Make the constraint store
            constraints = ConstraintSet()
            #make the ethereum world state
            world = evm.EVMWorld(constraints)

            address = 0x222222222222222222222222222222222222200
            balance = None
            code = 'U'
            storage = {3618502788666131106986593281521497120414687020801267626233049500247285301263: 3618502788666131106986593281521497120414687020801267626233049500247285301263}
            world.create_account( address=address, balance=balance, code=code, storage=storage)

            address=0x222222222222222222222222222222222222200
            caller=origin=0x111111111111111111111111111111111111100
            price=0
            value=10000
            bytecode='U'
            data = 'AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA'
            header = { 'coinbase': 0,
                        'timestamp': 0,
                        'number': 0,
                        'difficulty': 0,
                        'gaslimit': 0,
                        }
            gas = 1000000

            new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, gas=gas, world=world)
            new_vm._push(3618502788666131106986593281521497120414687020801267626233049500247285301263)
            new_vm._push(3618502788666131106986593281521497120414687020801267626233049500247285301263)
            last_exception, last_returned = self._execute(new_vm)
            self.assertEqual(last_exception, None)
            self.assertEqual(new_vm.pc, 1)
            self.assertEqual(new_vm.stack, [])

    def test_SSTORE_42(self):
            #Make the constraint store
            constraints = ConstraintSet()
            #make the ethereum world state
            world = evm.EVMWorld(constraints)

            address = 0x222222222222222222222222222222222222200
            balance = None
            code = 'U'
            storage = {16: 3618502788666131106986593281521497120414687020801267626233049500247285301263}
            world.create_account( address=address, balance=balance, code=code, storage=storage)

            address=0x222222222222222222222222222222222222200
            caller=origin=0x111111111111111111111111111111111111100
            price=0
            value=10000
            bytecode='U'
            data = 'AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA'
            header = { 'coinbase': 0,
                        'timestamp': 0,
                        'number': 0,
                        'difficulty': 0,
                        'gaslimit': 0,
                        }
            gas = 1000000

            new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, gas=gas, world=world)
            new_vm._push(3618502788666131106986593281521497120414687020801267626233049500247285301263)
            new_vm._push(16)
            last_exception, last_returned = self._execute(new_vm)
            self.assertEqual(last_exception, None)
            self.assertEqual(new_vm.pc, 1)
            self.assertEqual(new_vm.stack, [])

    def test_SSTORE_43(self):
            #Make the constraint store
            constraints = ConstraintSet()
            #make the ethereum world state
            world = evm.EVMWorld(constraints)

            address = 0x222222222222222222222222222222222222200
            balance = None
            code = 'U'
            storage = {32: 3618502788666131106986593281521497120414687020801267626233049500247285301263}
            world.create_account( address=address, balance=balance, code=code, storage=storage)

            address=0x222222222222222222222222222222222222200
            caller=origin=0x111111111111111111111111111111111111100
            price=0
            value=10000
            bytecode='U'
            data = 'AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA'
            header = { 'coinbase': 0,
                        'timestamp': 0,
                        'number': 0,
                        'difficulty': 0,
                        'gaslimit': 0,
                        }
            gas = 1000000

            new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, gas=gas, world=world)
            new_vm._push(3618502788666131106986593281521497120414687020801267626233049500247285301263)
            new_vm._push(32)
            last_exception, last_returned = self._execute(new_vm)
            self.assertEqual(last_exception, None)
            self.assertEqual(new_vm.pc, 1)
            self.assertEqual(new_vm.stack, [])

    def test_SSTORE_44(self):
            #Make the constraint store
            constraints = ConstraintSet()
            #make the ethereum world state
            world = evm.EVMWorld(constraints)

            address = 0x222222222222222222222222222222222222200
            balance = None
            code = 'U'
            storage = {48: 3618502788666131106986593281521497120414687020801267626233049500247285301263}
            world.create_account( address=address, balance=balance, code=code, storage=storage)

            address=0x222222222222222222222222222222222222200
            caller=origin=0x111111111111111111111111111111111111100
            price=0
            value=10000
            bytecode='U'
            data = 'AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA'
            header = { 'coinbase': 0,
                        'timestamp': 0,
                        'number': 0,
                        'difficulty': 0,
                        'gaslimit': 0,
                        }
            gas = 1000000

            new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, gas=gas, world=world)
            new_vm._push(3618502788666131106986593281521497120414687020801267626233049500247285301263)
            new_vm._push(48)
            last_exception, last_returned = self._execute(new_vm)
            self.assertEqual(last_exception, None)
            self.assertEqual(new_vm.pc, 1)
            self.assertEqual(new_vm.stack, [])

    def test_SSTORE_45(self):
            #Make the constraint store
            constraints = ConstraintSet()
            #make the ethereum world state
            world = evm.EVMWorld(constraints)

            address = 0x222222222222222222222222222222222222200
            balance = None
            code = 'U'
            storage = {6089590155545428825848686802984512581899718912: 3618502788666131106986593281521497120414687020801267626233049500247285301263}
            world.create_account( address=address, balance=balance, code=code, storage=storage)

            address=0x222222222222222222222222222222222222200
            caller=origin=0x111111111111111111111111111111111111100
            price=0
            value=10000
            bytecode='U'
            data = 'AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA'
            header = { 'coinbase': 0,
                        'timestamp': 0,
                        'number': 0,
                        'difficulty': 0,
                        'gaslimit': 0,
                        }
            gas = 1000000

            new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, gas=gas, world=world)
            new_vm._push(3618502788666131106986593281521497120414687020801267626233049500247285301263)
            new_vm._push(6089590155545428825848686802984512581899718912)
            last_exception, last_returned = self._execute(new_vm)
            self.assertEqual(last_exception, None)
            self.assertEqual(new_vm.pc, 1)
            self.assertEqual(new_vm.stack, [])

    def test_SSTORE_46(self):
            #Make the constraint store
            constraints = ConstraintSet()
            #make the ethereum world state
            world = evm.EVMWorld(constraints)

            address = 0x222222222222222222222222222222222222200
            balance = None
            code = 'U'
            storage = {115792089237316195423570985008687907853269984665640564039457584007913129639935: 16}
            world.create_account( address=address, balance=balance, code=code, storage=storage)

            address=0x222222222222222222222222222222222222200
            caller=origin=0x111111111111111111111111111111111111100
            price=0
            value=10000
            bytecode='U'
            data = 'AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA'
            header = { 'coinbase': 0,
                        'timestamp': 0,
                        'number': 0,
                        'difficulty': 0,
                        'gaslimit': 0,
                        }
            gas = 1000000

            new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, gas=gas, world=world)
            new_vm._push(16)
            new_vm._push(115792089237316195423570985008687907853269984665640564039457584007913129639935)
            last_exception, last_returned = self._execute(new_vm)
            self.assertEqual(last_exception, None)
            self.assertEqual(new_vm.pc, 1)
            self.assertEqual(new_vm.stack, [])

    def test_SSTORE_47(self):
            #Make the constraint store
            constraints = ConstraintSet()
            #make the ethereum world state
            world = evm.EVMWorld(constraints)

            address = 0x222222222222222222222222222222222222200
            balance = None
            code = 'U'
            storage = {0: 16}
            world.create_account( address=address, balance=balance, code=code, storage=storage)

            address=0x222222222222222222222222222222222222200
            caller=origin=0x111111111111111111111111111111111111100
            price=0
            value=10000
            bytecode='U'
            data = 'AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA'
            header = { 'coinbase': 0,
                        'timestamp': 0,
                        'number': 0,
                        'difficulty': 0,
                        'gaslimit': 0,
                        }
            gas = 1000000

            new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, gas=gas, world=world)
            new_vm._push(16)
            new_vm._push(0)
            last_exception, last_returned = self._execute(new_vm)
            self.assertEqual(last_exception, None)
            self.assertEqual(new_vm.pc, 1)
            self.assertEqual(new_vm.stack, [])

    def test_SSTORE_48(self):
            #Make the constraint store
            constraints = ConstraintSet()
            #make the ethereum world state
            world = evm.EVMWorld(constraints)

            address = 0x222222222222222222222222222222222222200
            balance = None
            code = 'U'
            storage = {1: 16}
            world.create_account( address=address, balance=balance, code=code, storage=storage)

            address=0x222222222222222222222222222222222222200
            caller=origin=0x111111111111111111111111111111111111100
            price=0
            value=10000
            bytecode='U'
            data = 'AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA'
            header = { 'coinbase': 0,
                        'timestamp': 0,
                        'number': 0,
                        'difficulty': 0,
                        'gaslimit': 0,
                        }
            gas = 1000000

            new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, gas=gas, world=world)
            new_vm._push(16)
            new_vm._push(1)
            last_exception, last_returned = self._execute(new_vm)
            self.assertEqual(last_exception, None)
            self.assertEqual(new_vm.pc, 1)
            self.assertEqual(new_vm.stack, [])

    def test_SSTORE_49(self):
            #Make the constraint store
            constraints = ConstraintSet()
            #make the ethereum world state
            world = evm.EVMWorld(constraints)

            address = 0x222222222222222222222222222222222222200
            balance = None
            code = 'U'
            storage = {57896044618658097711785492504343953926634992332820282019728792003956564819952: 16}
            world.create_account( address=address, balance=balance, code=code, storage=storage)

            address=0x222222222222222222222222222222222222200
            caller=origin=0x111111111111111111111111111111111111100
            price=0
            value=10000
            bytecode='U'
            data = 'AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA'
            header = { 'coinbase': 0,
                        'timestamp': 0,
                        'number': 0,
                        'difficulty': 0,
                        'gaslimit': 0,
                        }
            gas = 1000000

            new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, gas=gas, world=world)
            new_vm._push(16)
            new_vm._push(57896044618658097711785492504343953926634992332820282019728792003956564819952)
            last_exception, last_returned = self._execute(new_vm)
            self.assertEqual(last_exception, None)
            self.assertEqual(new_vm.pc, 1)
            self.assertEqual(new_vm.stack, [])

    def test_SSTORE_50(self):
            #Make the constraint store
            constraints = ConstraintSet()
            #make the ethereum world state
            world = evm.EVMWorld(constraints)

            address = 0x222222222222222222222222222222222222200
            balance = None
            code = 'U'
            storage = {3618502788666131106986593281521497120414687020801267626233049500247285301263: 16}
            world.create_account( address=address, balance=balance, code=code, storage=storage)

            address=0x222222222222222222222222222222222222200
            caller=origin=0x111111111111111111111111111111111111100
            price=0
            value=10000
            bytecode='U'
            data = 'AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA'
            header = { 'coinbase': 0,
                        'timestamp': 0,
                        'number': 0,
                        'difficulty': 0,
                        'gaslimit': 0,
                        }
            gas = 1000000

            new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, gas=gas, world=world)
            new_vm._push(16)
            new_vm._push(3618502788666131106986593281521497120414687020801267626233049500247285301263)
            last_exception, last_returned = self._execute(new_vm)
            self.assertEqual(last_exception, None)
            self.assertEqual(new_vm.pc, 1)
            self.assertEqual(new_vm.stack, [])

    def test_SSTORE_51(self):
            #Make the constraint store
            constraints = ConstraintSet()
            #make the ethereum world state
            world = evm.EVMWorld(constraints)

            address = 0x222222222222222222222222222222222222200
            balance = None
            code = 'U'
            storage = {16: 16}
            world.create_account( address=address, balance=balance, code=code, storage=storage)

            address=0x222222222222222222222222222222222222200
            caller=origin=0x111111111111111111111111111111111111100
            price=0
            value=10000
            bytecode='U'
            data = 'AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA'
            header = { 'coinbase': 0,
                        'timestamp': 0,
                        'number': 0,
                        'difficulty': 0,
                        'gaslimit': 0,
                        }
            gas = 1000000

            new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, gas=gas, world=world)
            new_vm._push(16)
            new_vm._push(16)
            last_exception, last_returned = self._execute(new_vm)
            self.assertEqual(last_exception, None)
            self.assertEqual(new_vm.pc, 1)
            self.assertEqual(new_vm.stack, [])

    def test_SSTORE_52(self):
            #Make the constraint store
            constraints = ConstraintSet()
            #make the ethereum world state
            world = evm.EVMWorld(constraints)

            address = 0x222222222222222222222222222222222222200
            balance = None
            code = 'U'
            storage = {32: 16}
            world.create_account( address=address, balance=balance, code=code, storage=storage)

            address=0x222222222222222222222222222222222222200
            caller=origin=0x111111111111111111111111111111111111100
            price=0
            value=10000
            bytecode='U'
            data = 'AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA'
            header = { 'coinbase': 0,
                        'timestamp': 0,
                        'number': 0,
                        'difficulty': 0,
                        'gaslimit': 0,
                        }
            gas = 1000000

            new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, gas=gas, world=world)
            new_vm._push(16)
            new_vm._push(32)
            last_exception, last_returned = self._execute(new_vm)
            self.assertEqual(last_exception, None)
            self.assertEqual(new_vm.pc, 1)
            self.assertEqual(new_vm.stack, [])

    def test_SSTORE_53(self):
            #Make the constraint store
            constraints = ConstraintSet()
            #make the ethereum world state
            world = evm.EVMWorld(constraints)

            address = 0x222222222222222222222222222222222222200
            balance = None
            code = 'U'
            storage = {48: 16}
            world.create_account( address=address, balance=balance, code=code, storage=storage)

            address=0x222222222222222222222222222222222222200
            caller=origin=0x111111111111111111111111111111111111100
            price=0
            value=10000
            bytecode='U'
            data = 'AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA'
            header = { 'coinbase': 0,
                        'timestamp': 0,
                        'number': 0,
                        'difficulty': 0,
                        'gaslimit': 0,
                        }
            gas = 1000000

            new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, gas=gas, world=world)
            new_vm._push(16)
            new_vm._push(48)
            last_exception, last_returned = self._execute(new_vm)
            self.assertEqual(last_exception, None)
            self.assertEqual(new_vm.pc, 1)
            self.assertEqual(new_vm.stack, [])

    def test_SSTORE_54(self):
            #Make the constraint store
            constraints = ConstraintSet()
            #make the ethereum world state
            world = evm.EVMWorld(constraints)

            address = 0x222222222222222222222222222222222222200
            balance = None
            code = 'U'
            storage = {6089590155545428825848686802984512581899718912: 16}
            world.create_account( address=address, balance=balance, code=code, storage=storage)

            address=0x222222222222222222222222222222222222200
            caller=origin=0x111111111111111111111111111111111111100
            price=0
            value=10000
            bytecode='U'
            data = 'AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA'
            header = { 'coinbase': 0,
                        'timestamp': 0,
                        'number': 0,
                        'difficulty': 0,
                        'gaslimit': 0,
                        }
            gas = 1000000

            new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, gas=gas, world=world)
            new_vm._push(16)
            new_vm._push(6089590155545428825848686802984512581899718912)
            last_exception, last_returned = self._execute(new_vm)
            self.assertEqual(last_exception, None)
            self.assertEqual(new_vm.pc, 1)
            self.assertEqual(new_vm.stack, [])

    def test_SSTORE_55(self):
            #Make the constraint store
            constraints = ConstraintSet()
            #make the ethereum world state
            world = evm.EVMWorld(constraints)

            address = 0x222222222222222222222222222222222222200
            balance = None
            code = 'U'
            storage = {115792089237316195423570985008687907853269984665640564039457584007913129639935: 32}
            world.create_account( address=address, balance=balance, code=code, storage=storage)

            address=0x222222222222222222222222222222222222200
            caller=origin=0x111111111111111111111111111111111111100
            price=0
            value=10000
            bytecode='U'
            data = 'AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA'
            header = { 'coinbase': 0,
                        'timestamp': 0,
                        'number': 0,
                        'difficulty': 0,
                        'gaslimit': 0,
                        }
            gas = 1000000

            new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, gas=gas, world=world)
            new_vm._push(32)
            new_vm._push(115792089237316195423570985008687907853269984665640564039457584007913129639935)
            last_exception, last_returned = self._execute(new_vm)
            self.assertEqual(last_exception, None)
            self.assertEqual(new_vm.pc, 1)
            self.assertEqual(new_vm.stack, [])

    def test_SSTORE_56(self):
            #Make the constraint store
            constraints = ConstraintSet()
            #make the ethereum world state
            world = evm.EVMWorld(constraints)

            address = 0x222222222222222222222222222222222222200
            balance = None
            code = 'U'
            storage = {0: 32}
            world.create_account( address=address, balance=balance, code=code, storage=storage)

            address=0x222222222222222222222222222222222222200
            caller=origin=0x111111111111111111111111111111111111100
            price=0
            value=10000
            bytecode='U'
            data = 'AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA'
            header = { 'coinbase': 0,
                        'timestamp': 0,
                        'number': 0,
                        'difficulty': 0,
                        'gaslimit': 0,
                        }
            gas = 1000000

            new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, gas=gas, world=world)
            new_vm._push(32)
            new_vm._push(0)
            last_exception, last_returned = self._execute(new_vm)
            self.assertEqual(last_exception, None)
            self.assertEqual(new_vm.pc, 1)
            self.assertEqual(new_vm.stack, [])

    def test_SSTORE_57(self):
            #Make the constraint store
            constraints = ConstraintSet()
            #make the ethereum world state
            world = evm.EVMWorld(constraints)

            address = 0x222222222222222222222222222222222222200
            balance = None
            code = 'U'
            storage = {1: 32}
            world.create_account( address=address, balance=balance, code=code, storage=storage)

            address=0x222222222222222222222222222222222222200
            caller=origin=0x111111111111111111111111111111111111100
            price=0
            value=10000
            bytecode='U'
            data = 'AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA'
            header = { 'coinbase': 0,
                        'timestamp': 0,
                        'number': 0,
                        'difficulty': 0,
                        'gaslimit': 0,
                        }
            gas = 1000000

            new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, gas=gas, world=world)
            new_vm._push(32)
            new_vm._push(1)
            last_exception, last_returned = self._execute(new_vm)
            self.assertEqual(last_exception, None)
            self.assertEqual(new_vm.pc, 1)
            self.assertEqual(new_vm.stack, [])

    def test_SSTORE_58(self):
            #Make the constraint store
            constraints = ConstraintSet()
            #make the ethereum world state
            world = evm.EVMWorld(constraints)

            address = 0x222222222222222222222222222222222222200
            balance = None
            code = 'U'
            storage = {57896044618658097711785492504343953926634992332820282019728792003956564819952: 32}
            world.create_account( address=address, balance=balance, code=code, storage=storage)

            address=0x222222222222222222222222222222222222200
            caller=origin=0x111111111111111111111111111111111111100
            price=0
            value=10000
            bytecode='U'
            data = 'AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA'
            header = { 'coinbase': 0,
                        'timestamp': 0,
                        'number': 0,
                        'difficulty': 0,
                        'gaslimit': 0,
                        }
            gas = 1000000

            new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, gas=gas, world=world)
            new_vm._push(32)
            new_vm._push(57896044618658097711785492504343953926634992332820282019728792003956564819952)
            last_exception, last_returned = self._execute(new_vm)
            self.assertEqual(last_exception, None)
            self.assertEqual(new_vm.pc, 1)
            self.assertEqual(new_vm.stack, [])

    def test_SSTORE_59(self):
            #Make the constraint store
            constraints = ConstraintSet()
            #make the ethereum world state
            world = evm.EVMWorld(constraints)

            address = 0x222222222222222222222222222222222222200
            balance = None
            code = 'U'
            storage = {3618502788666131106986593281521497120414687020801267626233049500247285301263: 32}
            world.create_account( address=address, balance=balance, code=code, storage=storage)

            address=0x222222222222222222222222222222222222200
            caller=origin=0x111111111111111111111111111111111111100
            price=0
            value=10000
            bytecode='U'
            data = 'AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA'
            header = { 'coinbase': 0,
                        'timestamp': 0,
                        'number': 0,
                        'difficulty': 0,
                        'gaslimit': 0,
                        }
            gas = 1000000

            new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, gas=gas, world=world)
            new_vm._push(32)
            new_vm._push(3618502788666131106986593281521497120414687020801267626233049500247285301263)
            last_exception, last_returned = self._execute(new_vm)
            self.assertEqual(last_exception, None)
            self.assertEqual(new_vm.pc, 1)
            self.assertEqual(new_vm.stack, [])

    def test_SSTORE_60(self):
            #Make the constraint store
            constraints = ConstraintSet()
            #make the ethereum world state
            world = evm.EVMWorld(constraints)

            address = 0x222222222222222222222222222222222222200
            balance = None
            code = 'U'
            storage = {16: 32}
            world.create_account( address=address, balance=balance, code=code, storage=storage)

            address=0x222222222222222222222222222222222222200
            caller=origin=0x111111111111111111111111111111111111100
            price=0
            value=10000
            bytecode='U'
            data = 'AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA'
            header = { 'coinbase': 0,
                        'timestamp': 0,
                        'number': 0,
                        'difficulty': 0,
                        'gaslimit': 0,
                        }
            gas = 1000000

            new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, gas=gas, world=world)
            new_vm._push(32)
            new_vm._push(16)
            last_exception, last_returned = self._execute(new_vm)
            self.assertEqual(last_exception, None)
            self.assertEqual(new_vm.pc, 1)
            self.assertEqual(new_vm.stack, [])

    def test_SSTORE_61(self):
            #Make the constraint store
            constraints = ConstraintSet()
            #make the ethereum world state
            world = evm.EVMWorld(constraints)

            address = 0x222222222222222222222222222222222222200
            balance = None
            code = 'U'
            storage = {32: 32}
            world.create_account( address=address, balance=balance, code=code, storage=storage)

            address=0x222222222222222222222222222222222222200
            caller=origin=0x111111111111111111111111111111111111100
            price=0
            value=10000
            bytecode='U'
            data = 'AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA'
            header = { 'coinbase': 0,
                        'timestamp': 0,
                        'number': 0,
                        'difficulty': 0,
                        'gaslimit': 0,
                        }
            gas = 1000000

            new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, gas=gas, world=world)
            new_vm._push(32)
            new_vm._push(32)
            last_exception, last_returned = self._execute(new_vm)
            self.assertEqual(last_exception, None)
            self.assertEqual(new_vm.pc, 1)
            self.assertEqual(new_vm.stack, [])

    def test_SSTORE_62(self):
            #Make the constraint store
            constraints = ConstraintSet()
            #make the ethereum world state
            world = evm.EVMWorld(constraints)

            address = 0x222222222222222222222222222222222222200
            balance = None
            code = 'U'
            storage = {48: 32}
            world.create_account( address=address, balance=balance, code=code, storage=storage)

            address=0x222222222222222222222222222222222222200
            caller=origin=0x111111111111111111111111111111111111100
            price=0
            value=10000
            bytecode='U'
            data = 'AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA'
            header = { 'coinbase': 0,
                        'timestamp': 0,
                        'number': 0,
                        'difficulty': 0,
                        'gaslimit': 0,
                        }
            gas = 1000000

            new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, gas=gas, world=world)
            new_vm._push(32)
            new_vm._push(48)
            last_exception, last_returned = self._execute(new_vm)
            self.assertEqual(last_exception, None)
            self.assertEqual(new_vm.pc, 1)
            self.assertEqual(new_vm.stack, [])

    def test_SSTORE_63(self):
            #Make the constraint store
            constraints = ConstraintSet()
            #make the ethereum world state
            world = evm.EVMWorld(constraints)

            address = 0x222222222222222222222222222222222222200
            balance = None
            code = 'U'
            storage = {6089590155545428825848686802984512581899718912: 32}
            world.create_account( address=address, balance=balance, code=code, storage=storage)

            address=0x222222222222222222222222222222222222200
            caller=origin=0x111111111111111111111111111111111111100
            price=0
            value=10000
            bytecode='U'
            data = 'AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA'
            header = { 'coinbase': 0,
                        'timestamp': 0,
                        'number': 0,
                        'difficulty': 0,
                        'gaslimit': 0,
                        }
            gas = 1000000

            new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, gas=gas, world=world)
            new_vm._push(32)
            new_vm._push(6089590155545428825848686802984512581899718912)
            last_exception, last_returned = self._execute(new_vm)
            self.assertEqual(last_exception, None)
            self.assertEqual(new_vm.pc, 1)
            self.assertEqual(new_vm.stack, [])

    def test_SSTORE_64(self):
            #Make the constraint store
            constraints = ConstraintSet()
            #make the ethereum world state
            world = evm.EVMWorld(constraints)

            address = 0x222222222222222222222222222222222222200
            balance = None
            code = 'U'
            storage = {115792089237316195423570985008687907853269984665640564039457584007913129639935: 48}
            world.create_account( address=address, balance=balance, code=code, storage=storage)

            address=0x222222222222222222222222222222222222200
            caller=origin=0x111111111111111111111111111111111111100
            price=0
            value=10000
            bytecode='U'
            data = 'AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA'
            header = { 'coinbase': 0,
                        'timestamp': 0,
                        'number': 0,
                        'difficulty': 0,
                        'gaslimit': 0,
                        }
            gas = 1000000

            new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, gas=gas, world=world)
            new_vm._push(48)
            new_vm._push(115792089237316195423570985008687907853269984665640564039457584007913129639935)
            last_exception, last_returned = self._execute(new_vm)
            self.assertEqual(last_exception, None)
            self.assertEqual(new_vm.pc, 1)
            self.assertEqual(new_vm.stack, [])

    def test_SSTORE_65(self):
            #Make the constraint store
            constraints = ConstraintSet()
            #make the ethereum world state
            world = evm.EVMWorld(constraints)

            address = 0x222222222222222222222222222222222222200
            balance = None
            code = 'U'
            storage = {0: 48}
            world.create_account( address=address, balance=balance, code=code, storage=storage)

            address=0x222222222222222222222222222222222222200
            caller=origin=0x111111111111111111111111111111111111100
            price=0
            value=10000
            bytecode='U'
            data = 'AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA'
            header = { 'coinbase': 0,
                        'timestamp': 0,
                        'number': 0,
                        'difficulty': 0,
                        'gaslimit': 0,
                        }
            gas = 1000000

            new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, gas=gas, world=world)
            new_vm._push(48)
            new_vm._push(0)
            last_exception, last_returned = self._execute(new_vm)
            self.assertEqual(last_exception, None)
            self.assertEqual(new_vm.pc, 1)
            self.assertEqual(new_vm.stack, [])

    def test_SSTORE_66(self):
            #Make the constraint store
            constraints = ConstraintSet()
            #make the ethereum world state
            world = evm.EVMWorld(constraints)

            address = 0x222222222222222222222222222222222222200
            balance = None
            code = 'U'
            storage = {1: 48}
            world.create_account( address=address, balance=balance, code=code, storage=storage)

            address=0x222222222222222222222222222222222222200
            caller=origin=0x111111111111111111111111111111111111100
            price=0
            value=10000
            bytecode='U'
            data = 'AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA'
            header = { 'coinbase': 0,
                        'timestamp': 0,
                        'number': 0,
                        'difficulty': 0,
                        'gaslimit': 0,
                        }
            gas = 1000000

            new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, gas=gas, world=world)
            new_vm._push(48)
            new_vm._push(1)
            last_exception, last_returned = self._execute(new_vm)
            self.assertEqual(last_exception, None)
            self.assertEqual(new_vm.pc, 1)
            self.assertEqual(new_vm.stack, [])

    def test_SSTORE_67(self):
            #Make the constraint store
            constraints = ConstraintSet()
            #make the ethereum world state
            world = evm.EVMWorld(constraints)

            address = 0x222222222222222222222222222222222222200
            balance = None
            code = 'U'
            storage = {57896044618658097711785492504343953926634992332820282019728792003956564819952: 48}
            world.create_account( address=address, balance=balance, code=code, storage=storage)

            address=0x222222222222222222222222222222222222200
            caller=origin=0x111111111111111111111111111111111111100
            price=0
            value=10000
            bytecode='U'
            data = 'AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA'
            header = { 'coinbase': 0,
                        'timestamp': 0,
                        'number': 0,
                        'difficulty': 0,
                        'gaslimit': 0,
                        }
            gas = 1000000

            new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, gas=gas, world=world)
            new_vm._push(48)
            new_vm._push(57896044618658097711785492504343953926634992332820282019728792003956564819952)
            last_exception, last_returned = self._execute(new_vm)
            self.assertEqual(last_exception, None)
            self.assertEqual(new_vm.pc, 1)
            self.assertEqual(new_vm.stack, [])

    def test_SSTORE_68(self):
            #Make the constraint store
            constraints = ConstraintSet()
            #make the ethereum world state
            world = evm.EVMWorld(constraints)

            address = 0x222222222222222222222222222222222222200
            balance = None
            code = 'U'
            storage = {3618502788666131106986593281521497120414687020801267626233049500247285301263: 48}
            world.create_account( address=address, balance=balance, code=code, storage=storage)

            address=0x222222222222222222222222222222222222200
            caller=origin=0x111111111111111111111111111111111111100
            price=0
            value=10000
            bytecode='U'
            data = 'AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA'
            header = { 'coinbase': 0,
                        'timestamp': 0,
                        'number': 0,
                        'difficulty': 0,
                        'gaslimit': 0,
                        }
            gas = 1000000

            new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, gas=gas, world=world)
            new_vm._push(48)
            new_vm._push(3618502788666131106986593281521497120414687020801267626233049500247285301263)
            last_exception, last_returned = self._execute(new_vm)
            self.assertEqual(last_exception, None)
            self.assertEqual(new_vm.pc, 1)
            self.assertEqual(new_vm.stack, [])

    def test_SSTORE_69(self):
            #Make the constraint store
            constraints = ConstraintSet()
            #make the ethereum world state
            world = evm.EVMWorld(constraints)

            address = 0x222222222222222222222222222222222222200
            balance = None
            code = 'U'
            storage = {16: 48}
            world.create_account( address=address, balance=balance, code=code, storage=storage)

            address=0x222222222222222222222222222222222222200
            caller=origin=0x111111111111111111111111111111111111100
            price=0
            value=10000
            bytecode='U'
            data = 'AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA'
            header = { 'coinbase': 0,
                        'timestamp': 0,
                        'number': 0,
                        'difficulty': 0,
                        'gaslimit': 0,
                        }
            gas = 1000000

            new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, gas=gas, world=world)
            new_vm._push(48)
            new_vm._push(16)
            last_exception, last_returned = self._execute(new_vm)
            self.assertEqual(last_exception, None)
            self.assertEqual(new_vm.pc, 1)
            self.assertEqual(new_vm.stack, [])

    def test_SSTORE_70(self):
            #Make the constraint store
            constraints = ConstraintSet()
            #make the ethereum world state
            world = evm.EVMWorld(constraints)

            address = 0x222222222222222222222222222222222222200
            balance = None
            code = 'U'
            storage = {32: 48}
            world.create_account( address=address, balance=balance, code=code, storage=storage)

            address=0x222222222222222222222222222222222222200
            caller=origin=0x111111111111111111111111111111111111100
            price=0
            value=10000
            bytecode='U'
            data = 'AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA'
            header = { 'coinbase': 0,
                        'timestamp': 0,
                        'number': 0,
                        'difficulty': 0,
                        'gaslimit': 0,
                        }
            gas = 1000000

            new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, gas=gas, world=world)
            new_vm._push(48)
            new_vm._push(32)
            last_exception, last_returned = self._execute(new_vm)
            self.assertEqual(last_exception, None)
            self.assertEqual(new_vm.pc, 1)
            self.assertEqual(new_vm.stack, [])

    def test_SSTORE_71(self):
            #Make the constraint store
            constraints = ConstraintSet()
            #make the ethereum world state
            world = evm.EVMWorld(constraints)

            address = 0x222222222222222222222222222222222222200
            balance = None
            code = 'U'
            storage = {48: 48}
            world.create_account( address=address, balance=balance, code=code, storage=storage)

            address=0x222222222222222222222222222222222222200
            caller=origin=0x111111111111111111111111111111111111100
            price=0
            value=10000
            bytecode='U'
            data = 'AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA'
            header = { 'coinbase': 0,
                        'timestamp': 0,
                        'number': 0,
                        'difficulty': 0,
                        'gaslimit': 0,
                        }
            gas = 1000000

            new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, gas=gas, world=world)
            new_vm._push(48)
            new_vm._push(48)
            last_exception, last_returned = self._execute(new_vm)
            self.assertEqual(last_exception, None)
            self.assertEqual(new_vm.pc, 1)
            self.assertEqual(new_vm.stack, [])

    def test_SSTORE_72(self):
            #Make the constraint store
            constraints = ConstraintSet()
            #make the ethereum world state
            world = evm.EVMWorld(constraints)

            address = 0x222222222222222222222222222222222222200
            balance = None
            code = 'U'
            storage = {6089590155545428825848686802984512581899718912: 48}
            world.create_account( address=address, balance=balance, code=code, storage=storage)

            address=0x222222222222222222222222222222222222200
            caller=origin=0x111111111111111111111111111111111111100
            price=0
            value=10000
            bytecode='U'
            data = 'AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA'
            header = { 'coinbase': 0,
                        'timestamp': 0,
                        'number': 0,
                        'difficulty': 0,
                        'gaslimit': 0,
                        }
            gas = 1000000

            new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, gas=gas, world=world)
            new_vm._push(48)
            new_vm._push(6089590155545428825848686802984512581899718912)
            last_exception, last_returned = self._execute(new_vm)
            self.assertEqual(last_exception, None)
            self.assertEqual(new_vm.pc, 1)
            self.assertEqual(new_vm.stack, [])

    def test_SSTORE_73(self):
            #Make the constraint store
            constraints = ConstraintSet()
            #make the ethereum world state
            world = evm.EVMWorld(constraints)

            address = 0x222222222222222222222222222222222222200
            balance = None
            code = 'U'
            storage = {115792089237316195423570985008687907853269984665640564039457584007913129639935: 6089590155545428825848686802984512581899718912}
            world.create_account( address=address, balance=balance, code=code, storage=storage)

            address=0x222222222222222222222222222222222222200
            caller=origin=0x111111111111111111111111111111111111100
            price=0
            value=10000
            bytecode='U'
            data = 'AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA'
            header = { 'coinbase': 0,
                        'timestamp': 0,
                        'number': 0,
                        'difficulty': 0,
                        'gaslimit': 0,
                        }
            gas = 1000000

            new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, gas=gas, world=world)
            new_vm._push(6089590155545428825848686802984512581899718912)
            new_vm._push(115792089237316195423570985008687907853269984665640564039457584007913129639935)
            last_exception, last_returned = self._execute(new_vm)
            self.assertEqual(last_exception, None)
            self.assertEqual(new_vm.pc, 1)
            self.assertEqual(new_vm.stack, [])

    def test_SSTORE_74(self):
            #Make the constraint store
            constraints = ConstraintSet()
            #make the ethereum world state
            world = evm.EVMWorld(constraints)

            address = 0x222222222222222222222222222222222222200
            balance = None
            code = 'U'
            storage = {0: 6089590155545428825848686802984512581899718912}
            world.create_account( address=address, balance=balance, code=code, storage=storage)

            address=0x222222222222222222222222222222222222200
            caller=origin=0x111111111111111111111111111111111111100
            price=0
            value=10000
            bytecode='U'
            data = 'AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA'
            header = { 'coinbase': 0,
                        'timestamp': 0,
                        'number': 0,
                        'difficulty': 0,
                        'gaslimit': 0,
                        }
            gas = 1000000

            new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, gas=gas, world=world)
            new_vm._push(6089590155545428825848686802984512581899718912)
            new_vm._push(0)
            last_exception, last_returned = self._execute(new_vm)
            self.assertEqual(last_exception, None)
            self.assertEqual(new_vm.pc, 1)
            self.assertEqual(new_vm.stack, [])

    def test_SSTORE_75(self):
            #Make the constraint store
            constraints = ConstraintSet()
            #make the ethereum world state
            world = evm.EVMWorld(constraints)

            address = 0x222222222222222222222222222222222222200
            balance = None
            code = 'U'
            storage = {1: 6089590155545428825848686802984512581899718912}
            world.create_account( address=address, balance=balance, code=code, storage=storage)

            address=0x222222222222222222222222222222222222200
            caller=origin=0x111111111111111111111111111111111111100
            price=0
            value=10000
            bytecode='U'
            data = 'AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA'
            header = { 'coinbase': 0,
                        'timestamp': 0,
                        'number': 0,
                        'difficulty': 0,
                        'gaslimit': 0,
                        }
            gas = 1000000

            new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, gas=gas, world=world)
            new_vm._push(6089590155545428825848686802984512581899718912)
            new_vm._push(1)
            last_exception, last_returned = self._execute(new_vm)
            self.assertEqual(last_exception, None)
            self.assertEqual(new_vm.pc, 1)
            self.assertEqual(new_vm.stack, [])

    def test_SSTORE_76(self):
            #Make the constraint store
            constraints = ConstraintSet()
            #make the ethereum world state
            world = evm.EVMWorld(constraints)

            address = 0x222222222222222222222222222222222222200
            balance = None
            code = 'U'
            storage = {57896044618658097711785492504343953926634992332820282019728792003956564819952: 6089590155545428825848686802984512581899718912}
            world.create_account( address=address, balance=balance, code=code, storage=storage)

            address=0x222222222222222222222222222222222222200
            caller=origin=0x111111111111111111111111111111111111100
            price=0
            value=10000
            bytecode='U'
            data = 'AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA'
            header = { 'coinbase': 0,
                        'timestamp': 0,
                        'number': 0,
                        'difficulty': 0,
                        'gaslimit': 0,
                        }
            gas = 1000000

            new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, gas=gas, world=world)
            new_vm._push(6089590155545428825848686802984512581899718912)
            new_vm._push(57896044618658097711785492504343953926634992332820282019728792003956564819952)
            last_exception, last_returned = self._execute(new_vm)
            self.assertEqual(last_exception, None)
            self.assertEqual(new_vm.pc, 1)
            self.assertEqual(new_vm.stack, [])

    def test_SSTORE_77(self):
            #Make the constraint store
            constraints = ConstraintSet()
            #make the ethereum world state
            world = evm.EVMWorld(constraints)

            address = 0x222222222222222222222222222222222222200
            balance = None
            code = 'U'
            storage = {3618502788666131106986593281521497120414687020801267626233049500247285301263: 6089590155545428825848686802984512581899718912}
            world.create_account( address=address, balance=balance, code=code, storage=storage)

            address=0x222222222222222222222222222222222222200
            caller=origin=0x111111111111111111111111111111111111100
            price=0
            value=10000
            bytecode='U'
            data = 'AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA'
            header = { 'coinbase': 0,
                        'timestamp': 0,
                        'number': 0,
                        'difficulty': 0,
                        'gaslimit': 0,
                        }
            gas = 1000000

            new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, gas=gas, world=world)
            new_vm._push(6089590155545428825848686802984512581899718912)
            new_vm._push(3618502788666131106986593281521497120414687020801267626233049500247285301263)
            last_exception, last_returned = self._execute(new_vm)
            self.assertEqual(last_exception, None)
            self.assertEqual(new_vm.pc, 1)
            self.assertEqual(new_vm.stack, [])

    def test_SSTORE_78(self):
            #Make the constraint store
            constraints = ConstraintSet()
            #make the ethereum world state
            world = evm.EVMWorld(constraints)

            address = 0x222222222222222222222222222222222222200
            balance = None
            code = 'U'
            storage = {16: 6089590155545428825848686802984512581899718912}
            world.create_account( address=address, balance=balance, code=code, storage=storage)

            address=0x222222222222222222222222222222222222200
            caller=origin=0x111111111111111111111111111111111111100
            price=0
            value=10000
            bytecode='U'
            data = 'AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA'
            header = { 'coinbase': 0,
                        'timestamp': 0,
                        'number': 0,
                        'difficulty': 0,
                        'gaslimit': 0,
                        }
            gas = 1000000

            new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, gas=gas, world=world)
            new_vm._push(6089590155545428825848686802984512581899718912)
            new_vm._push(16)
            last_exception, last_returned = self._execute(new_vm)
            self.assertEqual(last_exception, None)
            self.assertEqual(new_vm.pc, 1)
            self.assertEqual(new_vm.stack, [])

    def test_SSTORE_79(self):
            #Make the constraint store
            constraints = ConstraintSet()
            #make the ethereum world state
            world = evm.EVMWorld(constraints)

            address = 0x222222222222222222222222222222222222200
            balance = None
            code = 'U'
            storage = {32: 6089590155545428825848686802984512581899718912}
            world.create_account( address=address, balance=balance, code=code, storage=storage)

            address=0x222222222222222222222222222222222222200
            caller=origin=0x111111111111111111111111111111111111100
            price=0
            value=10000
            bytecode='U'
            data = 'AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA'
            header = { 'coinbase': 0,
                        'timestamp': 0,
                        'number': 0,
                        'difficulty': 0,
                        'gaslimit': 0,
                        }
            gas = 1000000

            new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, gas=gas, world=world)
            new_vm._push(6089590155545428825848686802984512581899718912)
            new_vm._push(32)
            last_exception, last_returned = self._execute(new_vm)
            self.assertEqual(last_exception, None)
            self.assertEqual(new_vm.pc, 1)
            self.assertEqual(new_vm.stack, [])

    def test_SSTORE_80(self):
            #Make the constraint store
            constraints = ConstraintSet()
            #make the ethereum world state
            world = evm.EVMWorld(constraints)

            address = 0x222222222222222222222222222222222222200
            balance = None
            code = 'U'
            storage = {48: 6089590155545428825848686802984512581899718912}
            world.create_account( address=address, balance=balance, code=code, storage=storage)

            address=0x222222222222222222222222222222222222200
            caller=origin=0x111111111111111111111111111111111111100
            price=0
            value=10000
            bytecode='U'
            data = 'AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA'
            header = { 'coinbase': 0,
                        'timestamp': 0,
                        'number': 0,
                        'difficulty': 0,
                        'gaslimit': 0,
                        }
            gas = 1000000

            new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, gas=gas, world=world)
            new_vm._push(6089590155545428825848686802984512581899718912)
            new_vm._push(48)
            last_exception, last_returned = self._execute(new_vm)
            self.assertEqual(last_exception, None)
            self.assertEqual(new_vm.pc, 1)
            self.assertEqual(new_vm.stack, [])

    def test_SSTORE_81(self):
            #Make the constraint store
            constraints = ConstraintSet()
            #make the ethereum world state
            world = evm.EVMWorld(constraints)

            address = 0x222222222222222222222222222222222222200
            balance = None
            code = 'U'
            storage = {6089590155545428825848686802984512581899718912: 6089590155545428825848686802984512581899718912}
            world.create_account( address=address, balance=balance, code=code, storage=storage)

            address=0x222222222222222222222222222222222222200
            caller=origin=0x111111111111111111111111111111111111100
            price=0
            value=10000
            bytecode='U'
            data = 'AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA'
            header = { 'coinbase': 0,
                        'timestamp': 0,
                        'number': 0,
                        'difficulty': 0,
                        'gaslimit': 0,
                        }
            gas = 1000000

            new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, gas=gas, world=world)
            new_vm._push(6089590155545428825848686802984512581899718912)
            new_vm._push(6089590155545428825848686802984512581899718912)
            last_exception, last_returned = self._execute(new_vm)
            self.assertEqual(last_exception, None)
            self.assertEqual(new_vm.pc, 1)
            self.assertEqual(new_vm.stack, [])

if __name__ == '__main__':
    unittest.main()
