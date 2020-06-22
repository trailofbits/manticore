import unittest

from manticore.core.smtlib import (
    ConstraintSet,
    Version,
    get_depth,
    Operators,
    translate_to_smtlib,
    simplify,
    arithmetic_simplify,
    constant_folder,
)
from manticore.core.smtlib.solver import Z3Solver
from manticore.core.smtlib.expression import *
from manticore.platforms.evm_world_state import (
    DefaultWorldState,
    DefaultWorldState,
    OverlayWorldState,
)
from manticore.utils.helpers import pickle_dumps

ADDRESS = 0x111111111111111111111111111111111111111

# sam.moelius: These tests were shamelessly copied from test_smtlibv2.py.


class StorageTest(unittest.TestCase):
    _multiprocess_can_split_ = True

    def setUp(self):
        self.solver = Z3Solver.instance()

    def assertItemsEqual(self, a, b):
        # Required for Python3 compatibility
        self.assertEqual(sorted(a), sorted(b))

    def tearDown(self):
        del self.solver

    def testBasicStorage(self):
        cs = ConstraintSet()
        # make storage
        world_state = OverlayWorldState(DefaultWorldState())
        # make free 256bit bitvectors
        key = cs.new_bitvec(256)
        value = cs.new_bitvec(256)
        other_key = cs.new_bitvec(256)
        other_value = cs.new_bitvec(256)
        # store two symbolic values at symbolic offsets
        world_state.set_storage_data(cs, ADDRESS, key, value)
        world_state.set_storage_data(cs, ADDRESS, other_key, other_value)

        # assert that the storage is 'A' at key position
        cs.add(world_state.get_storage_data(cs, ADDRESS, key) == ord("A"))

        # let's restrict key to be greater than 1000
        cs.add(key.ugt(1000))
        with cs as temp_cs:
            # 1001 position of storage can be 'A'
            temp_cs.add(world_state.get_storage_data(cs, ADDRESS, 1001) == ord("A"))
            self.assertTrue(self.solver.check(temp_cs))

        with cs as temp_cs:
            # 1001 position of storage can also be 'B'
            temp_cs.add(world_state.get_storage_data(cs, ADDRESS, 1001) == ord("B"))
            self.assertTrue(self.solver.check(temp_cs))

        with cs as temp_cs:
            # but if it is 'B' ...
            temp_cs.add(world_state.get_storage_data(cs, ADDRESS, 1001) == ord("B"))
            # then key can not be 1001
            temp_cs.add(key == 1001)
            self.assertFalse(self.solver.check(temp_cs))

        with cs as temp_cs:
            # If 1001 position is 'B' ...
            temp_cs.add(world_state.get_storage_data(cs, ADDRESS, 1001) == ord("B"))
            # then key can be 1000 for ex..
            temp_cs.add(key == 1002)
            self.assertTrue(self.solver.check(temp_cs))

    def testBasicStorage256(self):
        cs = ConstraintSet()
        # make storage
        world_state = OverlayWorldState(DefaultWorldState())
        # make free 256bit bitvectors
        key = cs.new_bitvec(256)
        value = cs.new_bitvec(256)
        other_key = cs.new_bitvec(256)
        other_value = cs.new_bitvec(256)
        # store two symbolic values at symbolic offsets
        world_state.set_storage_data(cs, ADDRESS, key, value)
        world_state.set_storage_data(cs, ADDRESS, other_key, other_value)

        # assert that the storage is 111...111 at key position
        cs.add(
            world_state.get_storage_data(cs, ADDRESS, key)
            == 11111111111111111111111111111111111111111111
        )
        # let's restrict key to be greater than 1000
        cs.add(key.ugt(1000))

        with cs as temp_cs:
            # 1001 position of storage can be 111...111
            temp_cs.add(
                world_state.get_storage_data(cs, ADDRESS, 1001)
                == 11111111111111111111111111111111111111111111
            )
            self.assertTrue(self.solver.check(temp_cs))

        with cs as temp_cs:
            # 1001 position of storage can also be 222...222
            temp_cs.add(
                world_state.get_storage_data(cs, ADDRESS, 1001)
                == 22222222222222222222222222222222222222222222
            )
            self.assertTrue(self.solver.check(temp_cs))

        with cs as temp_cs:
            # but if it is 222...222 ...
            temp_cs.add(
                world_state.get_storage_data(cs, ADDRESS, 1001)
                == 22222222222222222222222222222222222222222222
            )
            # then key can not be 1001
            temp_cs.add(key == 1001)
            self.assertFalse(self.solver.check(temp_cs))

        with cs as temp_cs:
            # If 1001 position is 222...222 ...
            temp_cs.add(
                world_state.get_storage_data(cs, ADDRESS, 1001)
                == 22222222222222222222222222222222222222222222
            )
            # then key can be 1002 for ex..
            temp_cs.add(key == 1002)
            self.assertTrue(self.solver.check(temp_cs))

    def testBasicStorageStore(self):
        cs = ConstraintSet()
        # make storage
        world_state = OverlayWorldState(DefaultWorldState())
        # make free 256bit bitvectors
        key = cs.new_bitvec(256)
        value = cs.new_bitvec(256)
        other_key = cs.new_bitvec(256)
        other_value = cs.new_bitvec(256)
        # store two symbolic values at symbolic offsets
        world_state.set_storage_data(cs, ADDRESS, key, value)
        world_state.set_storage_data(cs, ADDRESS, other_key, other_value)

        # assert that the storage is 'A' at key position
        world_state.set_storage_data(cs, ADDRESS, key, ord("A"))
        # let's restrict key to be greater than 1000
        cs.add(key.ugt(1000))

        # 1001 position of storage can be 'A'
        self.assertTrue(
            self.solver.can_be_true(cs, world_state.get_storage_data(cs, ADDRESS, 1001) == ord("A"))
        )

        # 1001 position of storage can be 'B'
        self.assertTrue(
            self.solver.can_be_true(cs, world_state.get_storage_data(cs, ADDRESS, 1001) == ord("B"))
        )

        with cs as temp_cs:
            # but if it is 'B' ...
            temp_cs.add(world_state.get_storage_data(cs, ADDRESS, 1001) == ord("B"))
            # then key can not be 1001
            temp_cs.add(key == 1001)
            self.assertFalse(self.solver.check(temp_cs))

        with cs as temp_cs:
            # If 1001 position is 'B' ...
            temp_cs.add(world_state.get_storage_data(cs, ADDRESS, 1001) == ord("B"))
            # then key can be 1002 for ex..
            temp_cs.add(key != 1002)
            self.assertTrue(self.solver.check(temp_cs))

    def testClosedWorldAssumption(self):
        cs = ConstraintSet()
        # make storage
        world_state = OverlayWorldState(DefaultWorldState())
        # make free 256bit bitvectors
        key = cs.new_bitvec(256)
        value = cs.new_bitvec(256)
        other_key = cs.new_bitvec(256)
        other_value = cs.new_bitvec(256)
        # store two symbolic values at symbolic offsets
        world_state.set_storage_data(cs, ADDRESS, key, value)
        world_state.set_storage_data(cs, ADDRESS, other_key, other_value)

        with cs as temp_cs:
            # sam.moelius: The value at 1001 can be 'A' and the value at 1002 can be 'B'.
            temp_cs.add(world_state.get_storage_data(cs, ADDRESS, 1001) == ord("A"))
            temp_cs.add(world_state.get_storage_data(cs, ADDRESS, 1002) == ord("B"))
            self.assertTrue(self.solver.check(temp_cs))

        with cs as temp_cs:
            # sam.moelius: If the value at 1001 is 'A' and the value at 1002 is 'B', then 'C'
            # cannot appear anywhere in storage.
            temp_cs.add(world_state.get_storage_data(cs, ADDRESS, 1001) == ord("A"))
            temp_cs.add(world_state.get_storage_data(cs, ADDRESS, 1002) == ord("B"))
            temp_cs.add(world_state.get_storage_data(cs, ADDRESS, key) == ord("C"))
            self.assertFalse(self.solver.check(temp_cs))

    def testBasicStorageSymbIdx(self):
        cs = ConstraintSet()
        world_state = OverlayWorldState(DefaultWorldState())
        key = cs.new_bitvec(256, name="key")
        index = cs.new_bitvec(256, name="index")

        world_state.set_storage_data(cs, ADDRESS, key, 1)  # Write 1 to a single location

        cs.add(
            world_state.get_storage_data(cs, ADDRESS, index) != 0
        )  # Constrain index so it selects that location

        cs.add(index != key)
        # key and index are the same there is only one slot in 1
        self.assertFalse(self.solver.check(cs))

    def testBasicStorageSymbIdx2(self):
        cs = ConstraintSet()
        world_state = OverlayWorldState(DefaultWorldState())
        key = cs.new_bitvec(256, name="key")
        index = cs.new_bitvec(256, name="index")

        world_state.set_storage_data(cs, ADDRESS, key, 1)  # Write 1 to a single location
        cs.add(
            world_state.get_storage_data(cs, ADDRESS, index) != 0
        )  # Constrain index so it selects that location
        a_index = self.solver.get_value(cs, index)  # get a concrete solution for index
        cs.add(
            world_state.get_storage_data(cs, ADDRESS, a_index) != 0
        )  # now storage must have something at that location
        cs.add(a_index != index)  # remove it from the solutions

        # It should not be another solution for index
        self.assertFalse(self.solver.check(cs))

    def testBasicStorageSymbIdx3(self):
        cs = ConstraintSet()
        world_state = OverlayWorldState(DefaultWorldState())
        key = cs.new_bitvec(256, name="key")
        index = cs.new_bitvec(256, name="index")

        world_state.set_storage_data(cs, ADDRESS, 0, 1)  # Write 1 to first location
        world_state.set_storage_data(
            cs, ADDRESS, key, 2
        )  # Write 2 to a symbolic (potentially any (potentially 0))location

        solutions = self.solver.get_all_values(
            cs, world_state.get_storage_data(cs, ADDRESS, 0)
        )  # get a concrete solution for index
        self.assertItemsEqual(solutions, (1, 2))

        solutions = self.solver.get_all_values(
            cs, world_state.get_storage_data(cs, ADDRESS, 0)
        )  # get a concrete solution for index 0
        self.assertItemsEqual(solutions, (1, 2))

        solutions = self.solver.get_all_values(
            cs, world_state.get_storage_data(cs, ADDRESS, 1)
        )  # get a concrete solution for index 1
        self.assertItemsEqual(solutions, (0, 2))

        # sam.moelius: Nothing that could be 12345 has been written to storage.
        self.assertFalse(
            self.solver.can_be_true(cs, world_state.get_storage_data(cs, ADDRESS, 1) == 12345)
        )

        # sam.moelius: Write a symbolic value at symbolic offset key.
        value = cs.new_bitvec(256, name="value")
        world_state.set_storage_data(cs, ADDRESS, key, value)

        # sam.moelius: Could 12345 appear at offset 1?  Yes, because value could be 12345 and key could be 1.
        self.assertTrue(
            self.solver.can_be_true(cs, world_state.get_storage_data(cs, ADDRESS, 1) == 12345)
        )

    def testBasicPickle(self):
        import pickle

        cs = ConstraintSet()

        # make storage
        world_state = OverlayWorldState(DefaultWorldState())
        # make free 256bit bitvector
        key = cs.new_bitvec(256)

        # assert that the storage is 'A' at key position
        world_state.set_storage_data(cs, ADDRESS, key, ord("A"))
        # let's restrict key to be greater than 1000
        cs.add(key.ugt(1000))
        cs = pickle.loads(pickle_dumps(cs))
        self.assertTrue(self.solver.check(cs))


if __name__ == "__main__":
    unittest.main()
