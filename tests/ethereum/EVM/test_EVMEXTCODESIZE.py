
import struct
import unittest
import json
from manticore.platforms import evm
from manticore.core import state
from manticore.core.smtlib import Operators, ConstraintSet
import os


class EVMTest_EXTCODESIZE(unittest.TestCase):
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
            last_exception = "INSUFFICIENT STACK"
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

    def test_EXTCODESIZE_1(self):
            #Make the constraint store
            constraints = ConstraintSet()
            #make the ethereum world state
            world = evm.EVMWorld(constraints)

            address = 0x66666666666666666666666666666666666666
            balance = None
            code = b''
            storage = {}
            world.create_account( address=address, balance=balance, code=code, storage=storage)

            address=0x222222222222222222222222222222222222200
            caller=origin=0x111111111111111111111111111111111111100
            price=0
            value=10000
            bytecode=b';'
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
            last_exception, last_returned = self._execute(new_vm)
            self.assertEqual(last_exception, None)
            self.assertEqual(new_vm.pc, 1)
            self.assertEqual(new_vm.stack, [0])

    def test_EXTCODESIZE_2(self):
            #Make the constraint store
            constraints = ConstraintSet()
            #make the ethereum world state
            world = evm.EVMWorld(constraints)

            address = 0x3030303030303030303030303030303030303030
            balance = None
            code = b''
            storage = {}
            world.create_account( address=address, balance=balance, code=code, storage=storage)

            address=0x222222222222222222222222222222222222200
            caller=origin=0x111111111111111111111111111111111111100
            price=0
            value=10000
            bytecode=b';'
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
            last_exception, last_returned = self._execute(new_vm)
            self.assertEqual(last_exception, None)
            self.assertEqual(new_vm.pc, 1)
            self.assertEqual(new_vm.stack, [0])

    def test_EXTCODESIZE_3(self):
            #Make the constraint store
            constraints = ConstraintSet()
            #make the ethereum world state
            world = evm.EVMWorld(constraints)

            address = 0x30303030303030303030303030303030303030
            balance = None
            code = b''
            storage = {}
            world.create_account( address=address, balance=balance, code=code, storage=storage)

            address=0x222222222222222222222222222222222222200
            caller=origin=0x111111111111111111111111111111111111100
            price=0
            value=10000
            bytecode=b';'
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
            last_exception, last_returned = self._execute(new_vm)
            self.assertEqual(last_exception, None)
            self.assertEqual(new_vm.pc, 1)
            self.assertEqual(new_vm.stack, [0])

    def test_EXTCODESIZE_4(self):
            #Make the constraint store
            constraints = ConstraintSet()
            #make the ethereum world state
            world = evm.EVMWorld(constraints)

            address = 0x66666666666666666666666666666666666666
            balance = None
            code = b''
            storage = {}
            world.create_account( address=address, balance=balance, code=code, storage=storage)

            address=0x222222222222222222222222222222222222200
            caller=origin=0x111111111111111111111111111111111111100
            price=0
            value=10000
            bytecode=b';'
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
            last_exception, last_returned = self._execute(new_vm)
            self.assertEqual(last_exception, None)
            self.assertEqual(new_vm.pc, 1)
            self.assertEqual(new_vm.stack, [0])

    def test_EXTCODESIZE_5(self):
            #Make the constraint store
            constraints = ConstraintSet()
            #make the ethereum world state
            world = evm.EVMWorld(constraints)

            address = 0x30303030303030303030303030303030303030
            balance = None
            code = b''
            storage = {}
            world.create_account( address=address, balance=balance, code=code, storage=storage)

            address=0x222222222222222222222222222222222222200
            caller=origin=0x111111111111111111111111111111111111100
            price=0
            value=10000
            bytecode=b';'
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
            last_exception, last_returned = self._execute(new_vm)
            self.assertEqual(last_exception, None)
            self.assertEqual(new_vm.pc, 1)
            self.assertEqual(new_vm.stack, [0])

    def test_EXTCODESIZE_6(self):
            #Make the constraint store
            constraints = ConstraintSet()
            #make the ethereum world state
            world = evm.EVMWorld(constraints)

            address = 0x30303030303030303030303030303030303030
            balance = None
            code = b''
            storage = {}
            world.create_account( address=address, balance=balance, code=code, storage=storage)

            address=0x222222222222222222222222222222222222200
            caller=origin=0x111111111111111111111111111111111111100
            price=0
            value=10000
            bytecode=b';'
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
            last_exception, last_returned = self._execute(new_vm)
            self.assertEqual(last_exception, None)
            self.assertEqual(new_vm.pc, 1)
            self.assertEqual(new_vm.stack, [0])

    def test_EXTCODESIZE_7(self):
            #Make the constraint store
            constraints = ConstraintSet()
            #make the ethereum world state
            world = evm.EVMWorld(constraints)

            address = 0x30303030303030303030303030303030303030
            balance = None
            code = b''
            storage = {}
            world.create_account( address=address, balance=balance, code=code, storage=storage)

            address=0x222222222222222222222222222222222222200
            caller=origin=0x111111111111111111111111111111111111100
            price=0
            value=10000
            bytecode=b';'
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
            last_exception, last_returned = self._execute(new_vm)
            self.assertEqual(last_exception, None)
            self.assertEqual(new_vm.pc, 1)
            self.assertEqual(new_vm.stack, [0])

    def test_EXTCODESIZE_8(self):
            #Make the constraint store
            constraints = ConstraintSet()
            #make the ethereum world state
            world = evm.EVMWorld(constraints)

            address = 0x30303030303030303030303030303030303030
            balance = None
            code = b''
            storage = {}
            world.create_account( address=address, balance=balance, code=code, storage=storage)

            address=0x222222222222222222222222222222222222200
            caller=origin=0x111111111111111111111111111111111111100
            price=0
            value=10000
            bytecode=b';'
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
            last_exception, last_returned = self._execute(new_vm)
            self.assertEqual(last_exception, None)
            self.assertEqual(new_vm.pc, 1)
            self.assertEqual(new_vm.stack, [0])

    def test_EXTCODESIZE_9(self):
            #Make the constraint store
            constraints = ConstraintSet()
            #make the ethereum world state
            world = evm.EVMWorld(constraints)

            address = 0x30313131313131313131313131313131313131
            balance = None
            code = b''
            storage = {}
            world.create_account( address=address, balance=balance, code=code, storage=storage)

            address=0x222222222222222222222222222222222222200
            caller=origin=0x111111111111111111111111111111111111100
            price=0
            value=10000
            bytecode=b';'
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
            last_exception, last_returned = self._execute(new_vm)
            self.assertEqual(last_exception, None)
            self.assertEqual(new_vm.pc, 1)
            self.assertEqual(new_vm.stack, [0])

if __name__ == '__main__':
    unittest.main()
