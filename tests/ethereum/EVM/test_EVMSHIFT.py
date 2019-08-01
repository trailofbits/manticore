import struct
import unittest
import json
from manticore.platforms import evm
from manticore.core import state
from manticore.core.smtlib import Operators, ConstraintSet
import os


class EVMTest_SHIFT(unittest.TestCase):
    _multiprocess_can_split_ = True
    maxDiff = None

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

    def test_SHL_0(self):
        # Make the constraint store
        constraints = ConstraintSet()
        # make the ethereum world state
        world = evm.EVMWorld(constraints)

        address = 0x222222222222222222222222222222222222200
        caller = 0x111111111111111111111111111111111111100
        value = 10000
        bytecode = b"\x1b"
        data = "AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA"
        gas = 1000000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, gas=gas, world=world)
        new_vm._push(1)
        new_vm._push(0)
        last_exception, last_returned = self._execute(new_vm)
        self.assertEqual(last_exception, None)
        self.assertEqual(new_vm.pc, 1)
        self.assertEqual(new_vm.stack, [1])

    def test_SHL_1(self):
        # Make the constraint store
        constraints = ConstraintSet()
        # make the ethereum world state
        world = evm.EVMWorld(constraints)

        address = 0x222222222222222222222222222222222222200
        caller = 0x111111111111111111111111111111111111100
        value = 10000
        bytecode = b"\x1b"
        data = "AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA"
        gas = 1000000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, gas=gas, world=world)
        new_vm._push(1)
        new_vm._push(1)
        last_exception, last_returned = self._execute(new_vm)
        self.assertEqual(last_exception, None)
        self.assertEqual(new_vm.pc, 1)
        self.assertEqual(new_vm.stack, [2])

    def test_SHL_2(self):
        # Make the constraint store
        constraints = ConstraintSet()
        # make the ethereum world state
        world = evm.EVMWorld(constraints)

        address = 0x222222222222222222222222222222222222200
        caller = 0x111111111111111111111111111111111111100
        value = 10000
        bytecode = b"\x1b"
        data = "AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA"
        gas = 1000000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, gas=gas, world=world)
        new_vm._push(1)
        new_vm._push(255)
        last_exception, last_returned = self._execute(new_vm)
        self.assertEqual(last_exception, None)
        self.assertEqual(new_vm.pc, 1)
        self.assertEqual(
            new_vm.stack,
            [57896044618658097711785492504343953926634992332820282019728792003956564819968],
        )

    def test_SHL_3(self):
        # Make the constraint store
        constraints = ConstraintSet()
        # make the ethereum world state
        world = evm.EVMWorld(constraints)

        address = 0x222222222222222222222222222222222222200
        caller = 0x111111111111111111111111111111111111100
        value = 10000
        bytecode = b"\x1b"
        data = "AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA"
        gas = 1000000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, gas=gas, world=world)
        new_vm._push(1)
        new_vm._push(256)
        last_exception, last_returned = self._execute(new_vm)
        self.assertEqual(last_exception, None)
        self.assertEqual(new_vm.pc, 1)
        self.assertEqual(new_vm.stack, [0])

    def test_SHL_4(self):
        # Make the constraint store
        constraints = ConstraintSet()
        # make the ethereum world state
        world = evm.EVMWorld(constraints)

        address = 0x222222222222222222222222222222222222200
        caller = 0x111111111111111111111111111111111111100
        value = 10000
        bytecode = b"\x1b"
        data = "AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA"
        gas = 1000000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, gas=gas, world=world)
        new_vm._push(1)
        new_vm._push(257)
        last_exception, last_returned = self._execute(new_vm)
        self.assertEqual(last_exception, None)
        self.assertEqual(new_vm.pc, 1)
        self.assertEqual(new_vm.stack, [0])

    def test_SHL_5(self):
        # Make the constraint store
        constraints = ConstraintSet()
        # make the ethereum world state
        world = evm.EVMWorld(constraints)

        address = 0x222222222222222222222222222222222222200
        caller = 0x111111111111111111111111111111111111100
        value = 10000
        bytecode = b"\x1b"
        data = "AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA"
        gas = 1000000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, gas=gas, world=world)
        new_vm._push(115792089237316195423570985008687907853269984665640564039457584007913129639935)
        new_vm._push(0)
        last_exception, last_returned = self._execute(new_vm)
        self.assertEqual(last_exception, None)
        self.assertEqual(new_vm.pc, 1)
        self.assertEqual(
            new_vm.stack,
            [115792089237316195423570985008687907853269984665640564039457584007913129639935],
        )

    def test_SHL_6(self):
        # Make the constraint store
        constraints = ConstraintSet()
        # make the ethereum world state
        world = evm.EVMWorld(constraints)

        address = 0x222222222222222222222222222222222222200
        caller = 0x111111111111111111111111111111111111100
        value = 10000
        bytecode = b"\x1b"
        data = "AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA"
        gas = 1000000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, gas=gas, world=world)
        new_vm._push(115792089237316195423570985008687907853269984665640564039457584007913129639935)
        new_vm._push(1)
        last_exception, last_returned = self._execute(new_vm)
        self.assertEqual(last_exception, None)
        self.assertEqual(new_vm.pc, 1)
        self.assertEqual(
            new_vm.stack,
            [115792089237316195423570985008687907853269984665640564039457584007913129639934],
        )

    def test_SHL_7(self):
        # Make the constraint store
        constraints = ConstraintSet()
        # make the ethereum world state
        world = evm.EVMWorld(constraints)

        address = 0x222222222222222222222222222222222222200
        caller = 0x111111111111111111111111111111111111100
        value = 10000
        bytecode = b"\x1b"
        data = "AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA"
        gas = 1000000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, gas=gas, world=world)
        new_vm._push(115792089237316195423570985008687907853269984665640564039457584007913129639935)
        new_vm._push(255)
        last_exception, last_returned = self._execute(new_vm)
        self.assertEqual(last_exception, None)
        self.assertEqual(new_vm.pc, 1)
        self.assertEqual(
            new_vm.stack,
            [57896044618658097711785492504343953926634992332820282019728792003956564819968],
        )

    def test_SHL_8(self):
        # Make the constraint store
        constraints = ConstraintSet()
        # make the ethereum world state
        world = evm.EVMWorld(constraints)

        address = 0x222222222222222222222222222222222222200
        caller = 0x111111111111111111111111111111111111100
        value = 10000
        bytecode = b"\x1b"
        data = "AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA"
        gas = 1000000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, gas=gas, world=world)
        new_vm._push(115792089237316195423570985008687907853269984665640564039457584007913129639935)
        new_vm._push(256)
        last_exception, last_returned = self._execute(new_vm)
        self.assertEqual(last_exception, None)
        self.assertEqual(new_vm.pc, 1)
        self.assertEqual(new_vm.stack, [0])

    def test_SHL_9(self):
        # Make the constraint store
        constraints = ConstraintSet()
        # make the ethereum world state
        world = evm.EVMWorld(constraints)

        address = 0x222222222222222222222222222222222222200
        caller = 0x111111111111111111111111111111111111100
        value = 10000
        bytecode = b"\x1b"
        data = "AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA"
        gas = 1000000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, gas=gas, world=world)
        new_vm._push(0)
        new_vm._push(1)
        last_exception, last_returned = self._execute(new_vm)
        self.assertEqual(last_exception, None)
        self.assertEqual(new_vm.pc, 1)
        self.assertEqual(new_vm.stack, [0])

    def test_SHL_10(self):
        # Make the constraint store
        constraints = ConstraintSet()
        # make the ethereum world state
        world = evm.EVMWorld(constraints)

        address = 0x222222222222222222222222222222222222200
        caller = 0x111111111111111111111111111111111111100
        value = 10000
        bytecode = b"\x1b"
        data = "AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA"
        gas = 1000000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, gas=gas, world=world)
        new_vm._push(57896044618658097711785492504343953926634992332820282019728792003956564819967)
        new_vm._push(1)
        last_exception, last_returned = self._execute(new_vm)
        self.assertEqual(last_exception, None)
        self.assertEqual(new_vm.pc, 1)
        self.assertEqual(
            new_vm.stack,
            [115792089237316195423570985008687907853269984665640564039457584007913129639934],
        )

    def test_SHR_0(self):
        # Make the constraint store
        constraints = ConstraintSet()
        # make the ethereum world state
        world = evm.EVMWorld(constraints)

        address = 0x222222222222222222222222222222222222200
        caller = 0x111111111111111111111111111111111111100
        value = 10000
        bytecode = b"\x1c"
        data = "AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA"
        gas = 1000000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, gas=gas, world=world)
        new_vm._push(1)
        new_vm._push(0)
        last_exception, last_returned = self._execute(new_vm)
        self.assertEqual(last_exception, None)
        self.assertEqual(new_vm.pc, 1)
        self.assertEqual(new_vm.stack, [1])

    def test_SHR_1(self):
        # Make the constraint store
        constraints = ConstraintSet()
        # make the ethereum world state
        world = evm.EVMWorld(constraints)

        address = 0x222222222222222222222222222222222222200
        caller = 0x111111111111111111111111111111111111100
        value = 10000
        bytecode = b"\x1c"
        data = "AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA"
        gas = 1000000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, gas=gas, world=world)
        new_vm._push(1)
        new_vm._push(1)
        last_exception, last_returned = self._execute(new_vm)
        self.assertEqual(last_exception, None)
        self.assertEqual(new_vm.pc, 1)
        self.assertEqual(new_vm.stack, [0])

    def test_SHR_2(self):
        # Make the constraint store
        constraints = ConstraintSet()
        # make the ethereum world state
        world = evm.EVMWorld(constraints)

        address = 0x222222222222222222222222222222222222200
        caller = 0x111111111111111111111111111111111111100
        value = 10000
        bytecode = b"\x1c"
        data = "AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA"
        gas = 1000000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, gas=gas, world=world)
        new_vm._push(57896044618658097711785492504343953926634992332820282019728792003956564819968)
        new_vm._push(1)
        last_exception, last_returned = self._execute(new_vm)
        self.assertEqual(last_exception, None)
        self.assertEqual(new_vm.pc, 1)
        self.assertEqual(
            new_vm.stack,
            [28948022309329048855892746252171976963317496166410141009864396001978282409984],
        )

    def test_SHR_3(self):
        # Make the constraint store
        constraints = ConstraintSet()
        # make the ethereum world state
        world = evm.EVMWorld(constraints)

        address = 0x222222222222222222222222222222222222200
        caller = 0x111111111111111111111111111111111111100
        value = 10000
        bytecode = b"\x1c"
        data = "AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA"
        gas = 1000000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, gas=gas, world=world)
        new_vm._push(57896044618658097711785492504343953926634992332820282019728792003956564819968)
        new_vm._push(255)
        last_exception, last_returned = self._execute(new_vm)
        self.assertEqual(last_exception, None)
        self.assertEqual(new_vm.pc, 1)
        self.assertEqual(new_vm.stack, [1])

    def test_SHR_4(self):
        # Make the constraint store
        constraints = ConstraintSet()
        # make the ethereum world state
        world = evm.EVMWorld(constraints)

        address = 0x222222222222222222222222222222222222200
        caller = 0x111111111111111111111111111111111111100
        value = 10000
        bytecode = b"\x1c"
        data = "AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA"
        gas = 1000000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, gas=gas, world=world)
        new_vm._push(57896044618658097711785492504343953926634992332820282019728792003956564819968)
        new_vm._push(256)
        last_exception, last_returned = self._execute(new_vm)
        self.assertEqual(last_exception, None)
        self.assertEqual(new_vm.pc, 1)
        self.assertEqual(new_vm.stack, [0])

    def test_SHR_5(self):
        # Make the constraint store
        constraints = ConstraintSet()
        # make the ethereum world state
        world = evm.EVMWorld(constraints)

        address = 0x222222222222222222222222222222222222200
        caller = 0x111111111111111111111111111111111111100
        value = 10000
        bytecode = b"\x1c"
        data = "AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA"
        gas = 1000000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, gas=gas, world=world)
        new_vm._push(57896044618658097711785492504343953926634992332820282019728792003956564819968)
        new_vm._push(257)
        last_exception, last_returned = self._execute(new_vm)
        self.assertEqual(last_exception, None)
        self.assertEqual(new_vm.pc, 1)
        self.assertEqual(new_vm.stack, [0])

    def test_SHR_6(self):
        # Make the constraint store
        constraints = ConstraintSet()
        # make the ethereum world state
        world = evm.EVMWorld(constraints)

        address = 0x222222222222222222222222222222222222200
        caller = 0x111111111111111111111111111111111111100
        value = 10000
        bytecode = b"\x1c"
        data = "AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA"
        gas = 1000000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, gas=gas, world=world)
        new_vm._push(115792089237316195423570985008687907853269984665640564039457584007913129639935)
        new_vm._push(0)
        last_exception, last_returned = self._execute(new_vm)
        self.assertEqual(last_exception, None)
        self.assertEqual(new_vm.pc, 1)
        self.assertEqual(
            new_vm.stack,
            [115792089237316195423570985008687907853269984665640564039457584007913129639935],
        )

    def test_SHR_7(self):
        # Make the constraint store
        constraints = ConstraintSet()
        # make the ethereum world state
        world = evm.EVMWorld(constraints)

        address = 0x222222222222222222222222222222222222200
        caller = 0x111111111111111111111111111111111111100
        value = 10000
        bytecode = b"\x1c"
        data = "AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA"
        gas = 1000000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, gas=gas, world=world)
        new_vm._push(115792089237316195423570985008687907853269984665640564039457584007913129639935)
        new_vm._push(1)
        last_exception, last_returned = self._execute(new_vm)
        self.assertEqual(last_exception, None)
        self.assertEqual(new_vm.pc, 1)
        self.assertEqual(
            new_vm.stack,
            [57896044618658097711785492504343953926634992332820282019728792003956564819967],
        )

    def test_SHR_8(self):
        # Make the constraint store
        constraints = ConstraintSet()
        # make the ethereum world state
        world = evm.EVMWorld(constraints)

        address = 0x222222222222222222222222222222222222200
        caller = 0x111111111111111111111111111111111111100
        value = 10000
        bytecode = b"\x1c"
        data = "AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA"
        gas = 1000000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, gas=gas, world=world)
        new_vm._push(115792089237316195423570985008687907853269984665640564039457584007913129639935)
        new_vm._push(255)
        last_exception, last_returned = self._execute(new_vm)
        self.assertEqual(last_exception, None)
        self.assertEqual(new_vm.pc, 1)
        self.assertEqual(new_vm.stack, [1])

    def test_SHR_9(self):
        # Make the constraint store
        constraints = ConstraintSet()
        # make the ethereum world state
        world = evm.EVMWorld(constraints)

        address = 0x222222222222222222222222222222222222200
        caller = 0x111111111111111111111111111111111111100
        value = 10000
        bytecode = b"\x1c"
        data = "AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA"
        gas = 1000000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, gas=gas, world=world)
        new_vm._push(115792089237316195423570985008687907853269984665640564039457584007913129639935)
        new_vm._push(256)
        last_exception, last_returned = self._execute(new_vm)
        self.assertEqual(last_exception, None)
        self.assertEqual(new_vm.pc, 1)
        self.assertEqual(new_vm.stack, [0])

    def test_SHR_10(self):
        # Make the constraint store
        constraints = ConstraintSet()
        # make the ethereum world state
        world = evm.EVMWorld(constraints)

        address = 0x222222222222222222222222222222222222200
        caller = 0x111111111111111111111111111111111111100
        value = 10000
        bytecode = b"\x1c"
        data = "AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA"
        gas = 1000000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, gas=gas, world=world)
        new_vm._push(0)
        new_vm._push(1)
        last_exception, last_returned = self._execute(new_vm)
        self.assertEqual(last_exception, None)
        self.assertEqual(new_vm.pc, 1)
        self.assertEqual(new_vm.stack, [0])

    def test_SAR_0(self):
        # Make the constraint store
        constraints = ConstraintSet()
        # make the ethereum world state
        world = evm.EVMWorld(constraints)

        address = 0x222222222222222222222222222222222222200
        caller = 0x111111111111111111111111111111111111100
        value = 10000
        bytecode = b"\x1d"
        data = "AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA"
        gas = 1000000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, gas=gas, world=world)
        new_vm._push(1)
        new_vm._push(0)
        last_exception, last_returned = self._execute(new_vm)
        self.assertEqual(last_exception, None)
        self.assertEqual(new_vm.pc, 1)
        self.assertEqual(new_vm.stack, [1])

    def test_SAR_1(self):
        # Make the constraint store
        constraints = ConstraintSet()
        # make the ethereum world state
        world = evm.EVMWorld(constraints)

        address = 0x222222222222222222222222222222222222200
        caller = 0x111111111111111111111111111111111111100
        value = 10000
        bytecode = b"\x1d"
        data = "AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA"
        gas = 1000000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, gas=gas, world=world)
        new_vm._push(1)
        new_vm._push(1)
        last_exception, last_returned = self._execute(new_vm)
        self.assertEqual(last_exception, None)
        self.assertEqual(new_vm.pc, 1)
        self.assertEqual(new_vm.stack, [0])

    def test_SAR_2(self):
        # Make the constraint store
        constraints = ConstraintSet()
        # make the ethereum world state
        world = evm.EVMWorld(constraints)

        address = 0x222222222222222222222222222222222222200
        caller = 0x111111111111111111111111111111111111100
        value = 10000
        bytecode = b"\x1d"
        data = "AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA"
        gas = 1000000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, gas=gas, world=world)
        new_vm._push(57896044618658097711785492504343953926634992332820282019728792003956564819968)
        new_vm._push(1)
        last_exception, last_returned = self._execute(new_vm)
        self.assertEqual(last_exception, None)
        self.assertEqual(new_vm.pc, 1)
        self.assertEqual(
            new_vm.stack,
            [86844066927987146567678238756515930889952488499230423029593188005934847229952],
        )

    def test_SAR_3(self):
        # Make the constraint store
        constraints = ConstraintSet()
        # make the ethereum world state
        world = evm.EVMWorld(constraints)

        address = 0x222222222222222222222222222222222222200
        caller = 0x111111111111111111111111111111111111100
        value = 10000
        bytecode = b"\x1d"
        data = "AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA"
        gas = 1000000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, gas=gas, world=world)
        new_vm._push(57896044618658097711785492504343953926634992332820282019728792003956564819968)
        new_vm._push(255)
        last_exception, last_returned = self._execute(new_vm)
        self.assertEqual(last_exception, None)
        self.assertEqual(new_vm.pc, 1)
        self.assertEqual(
            new_vm.stack,
            [115792089237316195423570985008687907853269984665640564039457584007913129639935],
        )

    def test_SAR_4(self):
        # Make the constraint store
        constraints = ConstraintSet()
        # make the ethereum world state
        world = evm.EVMWorld(constraints)

        address = 0x222222222222222222222222222222222222200
        caller = 0x111111111111111111111111111111111111100
        value = 10000
        bytecode = b"\x1d"
        data = "AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA"
        gas = 1000000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, gas=gas, world=world)
        new_vm._push(57896044618658097711785492504343953926634992332820282019728792003956564819968)
        new_vm._push(256)
        last_exception, last_returned = self._execute(new_vm)
        self.assertEqual(last_exception, None)
        self.assertEqual(new_vm.pc, 1)
        self.assertEqual(
            new_vm.stack,
            [115792089237316195423570985008687907853269984665640564039457584007913129639935],
        )

    def test_SAR_5(self):
        # Make the constraint store
        constraints = ConstraintSet()
        # make the ethereum world state
        world = evm.EVMWorld(constraints)

        address = 0x222222222222222222222222222222222222200
        caller = 0x111111111111111111111111111111111111100
        value = 10000
        bytecode = b"\x1d"
        data = "AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA"
        gas = 1000000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, gas=gas, world=world)
        new_vm._push(57896044618658097711785492504343953926634992332820282019728792003956564819968)
        new_vm._push(257)
        last_exception, last_returned = self._execute(new_vm)
        self.assertEqual(last_exception, None)
        self.assertEqual(new_vm.pc, 1)
        self.assertEqual(
            new_vm.stack,
            [115792089237316195423570985008687907853269984665640564039457584007913129639935],
        )

    def test_SAR_6(self):
        # Make the constraint store
        constraints = ConstraintSet()
        # make the ethereum world state
        world = evm.EVMWorld(constraints)

        address = 0x222222222222222222222222222222222222200
        caller = 0x111111111111111111111111111111111111100
        value = 10000
        bytecode = b"\x1d"
        data = "AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA"
        gas = 1000000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, gas=gas, world=world)
        new_vm._push(115792089237316195423570985008687907853269984665640564039457584007913129639935)
        new_vm._push(0)
        last_exception, last_returned = self._execute(new_vm)
        self.assertEqual(last_exception, None)
        self.assertEqual(new_vm.pc, 1)
        self.assertEqual(
            new_vm.stack,
            [115792089237316195423570985008687907853269984665640564039457584007913129639935],
        )

    def test_SAR_7(self):
        # Make the constraint store
        constraints = ConstraintSet()
        # make the ethereum world state
        world = evm.EVMWorld(constraints)

        address = 0x222222222222222222222222222222222222200
        caller = 0x111111111111111111111111111111111111100
        value = 10000
        bytecode = b"\x1d"
        data = "AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA"
        gas = 1000000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, gas=gas, world=world)
        new_vm._push(115792089237316195423570985008687907853269984665640564039457584007913129639935)
        new_vm._push(1)
        last_exception, last_returned = self._execute(new_vm)
        self.assertEqual(last_exception, None)
        self.assertEqual(new_vm.pc, 1)
        self.assertEqual(
            new_vm.stack,
            [115792089237316195423570985008687907853269984665640564039457584007913129639935],
        )

    def test_SAR_8(self):
        # Make the constraint store
        constraints = ConstraintSet()
        # make the ethereum world state
        world = evm.EVMWorld(constraints)

        address = 0x222222222222222222222222222222222222200
        caller = 0x111111111111111111111111111111111111100
        value = 10000
        bytecode = b"\x1d"
        data = "AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA"
        gas = 1000000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, gas=gas, world=world)
        new_vm._push(115792089237316195423570985008687907853269984665640564039457584007913129639935)
        new_vm._push(255)
        last_exception, last_returned = self._execute(new_vm)
        self.assertEqual(last_exception, None)
        self.assertEqual(new_vm.pc, 1)
        self.assertEqual(
            new_vm.stack,
            [115792089237316195423570985008687907853269984665640564039457584007913129639935],
        )

    def test_SAR_9(self):
        # Make the constraint store
        constraints = ConstraintSet()
        # make the ethereum world state
        world = evm.EVMWorld(constraints)

        address = 0x222222222222222222222222222222222222200
        caller = 0x111111111111111111111111111111111111100
        value = 10000
        bytecode = b"\x1d"
        data = "AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA"
        gas = 1000000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, gas=gas, world=world)
        new_vm._push(115792089237316195423570985008687907853269984665640564039457584007913129639935)
        new_vm._push(256)
        last_exception, last_returned = self._execute(new_vm)
        self.assertEqual(last_exception, None)
        self.assertEqual(new_vm.pc, 1)
        self.assertEqual(
            new_vm.stack,
            [115792089237316195423570985008687907853269984665640564039457584007913129639935],
        )

    def test_SAR_10(self):
        # Make the constraint store
        constraints = ConstraintSet()
        # make the ethereum world state
        world = evm.EVMWorld(constraints)

        address = 0x222222222222222222222222222222222222200
        caller = 0x111111111111111111111111111111111111100
        value = 10000
        bytecode = b"\x1d"
        data = "AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA"
        gas = 1000000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, gas=gas, world=world)
        new_vm._push(0)
        new_vm._push(1)
        last_exception, last_returned = self._execute(new_vm)
        self.assertEqual(last_exception, None)
        self.assertEqual(new_vm.pc, 1)
        self.assertEqual(new_vm.stack, [0])

    def test_SAR_11(self):
        # Make the constraint store
        constraints = ConstraintSet()
        # make the ethereum world state
        world = evm.EVMWorld(constraints)

        address = 0x222222222222222222222222222222222222200
        caller = 0x111111111111111111111111111111111111100
        value = 10000
        bytecode = b"\x1d"
        data = "AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA"
        gas = 1000000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, gas=gas, world=world)
        new_vm._push(28948022309329048855892746252171976963317496166410141009864396001978282409984)
        new_vm._push(254)
        last_exception, last_returned = self._execute(new_vm)
        self.assertEqual(last_exception, None)
        self.assertEqual(new_vm.pc, 1)
        self.assertEqual(new_vm.stack, [1])

    def test_SAR_12(self):
        # Make the constraint store
        constraints = ConstraintSet()
        # make the ethereum world state
        world = evm.EVMWorld(constraints)

        address = 0x222222222222222222222222222222222222200
        caller = 0x111111111111111111111111111111111111100
        value = 10000
        bytecode = b"\x1d"
        data = "AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA"
        gas = 1000000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, gas=gas, world=world)
        new_vm._push(57896044618658097711785492504343953926634992332820282019728792003956564819967)
        new_vm._push(248)
        last_exception, last_returned = self._execute(new_vm)
        self.assertEqual(last_exception, None)
        self.assertEqual(new_vm.pc, 1)
        self.assertEqual(new_vm.stack, [127])

    def test_SAR_13(self):
        # Make the constraint store
        constraints = ConstraintSet()
        # make the ethereum world state
        world = evm.EVMWorld(constraints)

        address = 0x222222222222222222222222222222222222200
        caller = 0x111111111111111111111111111111111111100
        value = 10000
        bytecode = b"\x1d"
        data = "AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA"
        gas = 1000000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, gas=gas, world=world)
        new_vm._push(57896044618658097711785492504343953926634992332820282019728792003956564819967)
        new_vm._push(254)
        last_exception, last_returned = self._execute(new_vm)
        self.assertEqual(last_exception, None)
        self.assertEqual(new_vm.pc, 1)
        self.assertEqual(new_vm.stack, [1])

    def test_SAR_14(self):
        # Make the constraint store
        constraints = ConstraintSet()
        # make the ethereum world state
        world = evm.EVMWorld(constraints)

        address = 0x222222222222222222222222222222222222200
        caller = 0x111111111111111111111111111111111111100
        value = 10000
        bytecode = b"\x1d"
        data = "AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA"
        gas = 1000000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, gas=gas, world=world)
        new_vm._push(57896044618658097711785492504343953926634992332820282019728792003956564819967)
        new_vm._push(255)
        last_exception, last_returned = self._execute(new_vm)
        self.assertEqual(last_exception, None)
        self.assertEqual(new_vm.pc, 1)
        self.assertEqual(new_vm.stack, [0])

    def test_SAR_15(self):
        # Make the constraint store
        constraints = ConstraintSet()
        # make the ethereum world state
        world = evm.EVMWorld(constraints)

        address = 0x222222222222222222222222222222222222200
        caller = 0x111111111111111111111111111111111111100
        value = 10000
        bytecode = b"\x1d"
        data = "AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA"
        gas = 1000000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, gas=gas, world=world)
        new_vm._push(57896044618658097711785492504343953926634992332820282019728792003956564819967)
        new_vm._push(256)
        last_exception, last_returned = self._execute(new_vm)
        self.assertEqual(last_exception, None)
        self.assertEqual(new_vm.pc, 1)
        self.assertEqual(new_vm.stack, [0])


if __name__ == "__main__":
    unittest.main()
