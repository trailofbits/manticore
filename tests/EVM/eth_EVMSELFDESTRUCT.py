
import struct
import unittest
import json
from manticore.platforms import evm
from manticore.core import state
from manticore.core.smtlib import Operators, ConstraintSet
import os


class EVMTest_SELFDESTRUCT(unittest.TestCase):
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
            last_exception = "SELFDESTRUCT"
        except evm.Return as e:
            last_exception = "RETURN"
            last_returned = e.data
        except evm.Revert:
            last_exception = "REVERT"
        except evm.EndTx as e:
            last_exception = e.result
            
        return last_exception, last_returned

    def test_SELFDESTRUCT_1(self):
            #Make the constraint store
            constraints = ConstraintSet()
            #make the ethereum world state
            world = evm.EVMWorld(constraints)

            address = 0x303232323232323232323232323232323232323
            balance = 0
            code = ''
            storage = {}
            world.create_account( address=address, balance=balance, code=code, storage=storage)

            address = 0xfffffffffffffffffffffffffffffffffffffff
            balance = 0
            code = ''
            storage = {}
            world.create_account( address=address, balance=balance, code=code, storage=storage)

            address = 0x111111111111111111111111111111111111100
            balance = 0
            code = ''
            storage = {}
            world.create_account( address=address, balance=balance, code=code, storage=storage)

            address = 0x222222222222222222222222222222222222200
            balance = 0
            code = ''
            storage = {}
            world.create_account( address=address, balance=balance, code=code, storage=storage)

            address=0x222222222222222222222222222222222222200
            caller=origin=0x111111111111111111111111111111111111100
            price=0
            value=10000
            bytecode='\xff'
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
            self.assertEqual(last_exception, 'SELFDESTRUCT')
            self.assertEqual(new_vm.gas, 995000)

    def test_SELFDESTRUCT_2(self):
            #Make the constraint store
            constraints = ConstraintSet()
            #make the ethereum world state
            world = evm.EVMWorld(constraints)

            address = 0x3032323232323232323232323232323232323230
            balance = 0
            code = ''
            storage = {}
            world.create_account( address=address, balance=balance, code=code, storage=storage)

            address = 0x0
            balance = 0
            code = ''
            storage = {}
            world.create_account( address=address, balance=balance, code=code, storage=storage)

            address = 0x111111111111111111111111111111111111100
            balance = 0
            code = ''
            storage = {}
            world.create_account( address=address, balance=balance, code=code, storage=storage)

            address = 0x222222222222222222222222222222222222200
            balance = 0
            code = ''
            storage = {}
            world.create_account( address=address, balance=balance, code=code, storage=storage)

            address=0x222222222222222222222222222222222222200
            caller=origin=0x111111111111111111111111111111111111100
            price=0
            value=10000
            bytecode='\xff'
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
            self.assertEqual(last_exception, 'SELFDESTRUCT')
            self.assertEqual(new_vm.gas, 995000)

    def test_SELFDESTRUCT_3(self):
            #Make the constraint store
            constraints = ConstraintSet()
            #make the ethereum world state
            world = evm.EVMWorld(constraints)

            address = 0x3032323232323232323232323232323232323230
            balance = 0
            code = ''
            storage = {}
            world.create_account( address=address, balance=balance, code=code, storage=storage)

            address = 0x1
            balance = 0
            code = ''
            storage = {}
            world.create_account( address=address, balance=balance, code=code, storage=storage)

            address = 0x111111111111111111111111111111111111100
            balance = 0
            code = ''
            storage = {}
            world.create_account( address=address, balance=balance, code=code, storage=storage)

            address = 0x222222222222222222222222222222222222200
            balance = 0
            code = ''
            storage = {}
            world.create_account( address=address, balance=balance, code=code, storage=storage)

            address=0x222222222222222222222222222222222222200
            caller=origin=0x111111111111111111111111111111111111100
            price=0
            value=10000
            bytecode='\xff'
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
            self.assertEqual(last_exception, 'SELFDESTRUCT')
            self.assertEqual(new_vm.gas, 995000)

    def test_SELFDESTRUCT_4(self):
            #Make the constraint store
            constraints = ConstraintSet()
            #make the ethereum world state
            world = evm.EVMWorld(constraints)

            address = 0x3032323232323232323232323232323232323230
            balance = 0
            code = ''
            storage = {}
            world.create_account( address=address, balance=balance, code=code, storage=storage)

            address = 0xfffffffffffffffffffffffffffffffffffffff0
            balance = 0
            code = ''
            storage = {}
            world.create_account( address=address, balance=balance, code=code, storage=storage)

            address = 0x111111111111111111111111111111111111100
            balance = 0
            code = ''
            storage = {}
            world.create_account( address=address, balance=balance, code=code, storage=storage)

            address = 0x222222222222222222222222222222222222200
            balance = 0
            code = ''
            storage = {}
            world.create_account( address=address, balance=balance, code=code, storage=storage)

            address=0x222222222222222222222222222222222222200
            caller=origin=0x111111111111111111111111111111111111100
            price=0
            value=10000
            bytecode='\xff'
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
            self.assertEqual(last_exception, 'SELFDESTRUCT')
            self.assertEqual(new_vm.gas, 995000)

    def test_SELFDESTRUCT_5(self):
            #Make the constraint store
            constraints = ConstraintSet()
            #make the ethereum world state
            world = evm.EVMWorld(constraints)

            address = 0x3032323232323232323232323232323232323230
            balance = 0
            code = ''
            storage = {}
            world.create_account( address=address, balance=balance, code=code, storage=storage)

            address = 0xf
            balance = 0
            code = ''
            storage = {}
            world.create_account( address=address, balance=balance, code=code, storage=storage)

            address = 0x111111111111111111111111111111111111100
            balance = 0
            code = ''
            storage = {}
            world.create_account( address=address, balance=balance, code=code, storage=storage)

            address = 0x222222222222222222222222222222222222200
            balance = 0
            code = ''
            storage = {}
            world.create_account( address=address, balance=balance, code=code, storage=storage)

            address=0x222222222222222222222222222222222222200
            caller=origin=0x111111111111111111111111111111111111100
            price=0
            value=10000
            bytecode='\xff'
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
            self.assertEqual(last_exception, 'SELFDESTRUCT')
            self.assertEqual(new_vm.gas, 995000)

    def test_SELFDESTRUCT_6(self):
            #Make the constraint store
            constraints = ConstraintSet()
            #make the ethereum world state
            world = evm.EVMWorld(constraints)

            address = 0x3032323232323232323232323232323232323230
            balance = 0
            code = ''
            storage = {}
            world.create_account( address=address, balance=balance, code=code, storage=storage)

            address = 0x10
            balance = 0
            code = ''
            storage = {}
            world.create_account( address=address, balance=balance, code=code, storage=storage)

            address = 0x111111111111111111111111111111111111100
            balance = 0
            code = ''
            storage = {}
            world.create_account( address=address, balance=balance, code=code, storage=storage)

            address = 0x222222222222222222222222222222222222200
            balance = 0
            code = ''
            storage = {}
            world.create_account( address=address, balance=balance, code=code, storage=storage)

            address=0x222222222222222222222222222222222222200
            caller=origin=0x111111111111111111111111111111111111100
            price=0
            value=10000
            bytecode='\xff'
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
            self.assertEqual(last_exception, 'SELFDESTRUCT')
            self.assertEqual(new_vm.gas, 995000)

    def test_SELFDESTRUCT_7(self):
            #Make the constraint store
            constraints = ConstraintSet()
            #make the ethereum world state
            world = evm.EVMWorld(constraints)

            address = 0x3032323232323232323232323232323232323230
            balance = 0
            code = ''
            storage = {}
            world.create_account( address=address, balance=balance, code=code, storage=storage)

            address = 0x20
            balance = 0
            code = ''
            storage = {}
            world.create_account( address=address, balance=balance, code=code, storage=storage)

            address = 0x111111111111111111111111111111111111100
            balance = 0
            code = ''
            storage = {}
            world.create_account( address=address, balance=balance, code=code, storage=storage)

            address = 0x222222222222222222222222222222222222200
            balance = 0
            code = ''
            storage = {}
            world.create_account( address=address, balance=balance, code=code, storage=storage)

            address=0x222222222222222222222222222222222222200
            caller=origin=0x111111111111111111111111111111111111100
            price=0
            value=10000
            bytecode='\xff'
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
            self.assertEqual(last_exception, 'SELFDESTRUCT')
            self.assertEqual(new_vm.gas, 995000)

    def test_SELFDESTRUCT_8(self):
            #Make the constraint store
            constraints = ConstraintSet()
            #make the ethereum world state
            world = evm.EVMWorld(constraints)

            address = 0x3032323232323232323232323232323232323230
            balance = 0
            code = ''
            storage = {}
            world.create_account( address=address, balance=balance, code=code, storage=storage)

            address = 0x30
            balance = 0
            code = ''
            storage = {}
            world.create_account( address=address, balance=balance, code=code, storage=storage)

            address = 0x111111111111111111111111111111111111100
            balance = 0
            code = ''
            storage = {}
            world.create_account( address=address, balance=balance, code=code, storage=storage)

            address = 0x222222222222222222222222222222222222200
            balance = 0
            code = ''
            storage = {}
            world.create_account( address=address, balance=balance, code=code, storage=storage)

            address=0x222222222222222222222222222222222222200
            caller=origin=0x111111111111111111111111111111111111100
            price=0
            value=10000
            bytecode='\xff'
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
            self.assertEqual(last_exception, 'SELFDESTRUCT')
            self.assertEqual(new_vm.gas, 995000)

    def test_SELFDESTRUCT_9(self):
            #Make the constraint store
            constraints = ConstraintSet()
            #make the ethereum world state
            world = evm.EVMWorld(constraints)

            address = 0x3032323232323232323232323232323232323230
            balance = 0
            code = ''
            storage = {}
            world.create_account( address=address, balance=balance, code=code, storage=storage)

            address = 0x111111111111111111111111111111111111100
            balance = 0
            code = ''
            storage = {}
            world.create_account( address=address, balance=balance, code=code, storage=storage)


            address = 0x222222222222222222222222222222222222200
            balance = 0
            code = ''
            storage = {}
            world.create_account( address=address, balance=balance, code=code, storage=storage)

            address=0x222222222222222222222222222222222222200
            caller=origin=0x111111111111111111111111111111111111100
            price=0
            value=10000
            bytecode='\xff'
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
            self.assertEqual(last_exception, 'SELFDESTRUCT')
            self.assertEqual(new_vm.gas, 995000)

if __name__ == '__main__':
    unittest.main()
