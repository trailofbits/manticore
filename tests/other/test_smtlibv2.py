import unittest
import os
import sys
from typing import Set, Type

from manticore.core.smtlib import (
    ConstraintSet,
    Version,
    get_depth,
    Operators,
    translate_to_smtlib,
    pretty_print,
    simplify,
    arithmetic_simplify,
    constant_folder,
    replace,
    BitVecConstant,
    BitVecExtract,
)
from manticore.core.smtlib.solver import (
    Z3Solver,
    YicesSolver,
    CVC4Solver,
    BoolectorSolver,
    PortfolioSolver,
)
from manticore.core.smtlib.expression import *
from manticore.utils.helpers import pickle_dumps
from manticore import config

# logging.basicConfig(filename = "test.log",
#                format = "%(asctime)s: %(name)s:%(levelname)s: %(message)s",
#                level = logging.DEBUG)

DIRPATH = os.path.dirname(__file__)


"""
class Z3Specific(unittest.TestCase):
    _multiprocess_can_split_ = True

    def setUp(self):
        self.solver = Z3Solver.instance()


    @patch('subprocess.check_output', mock_open())
    def test_check_solver_min(self, mock_check_output):
        mock_check_output.return_value = ("output", "Error")
        #mock_check_output.return_value='(:version "4.4.1")'
        #mock_function = create_autospec(function, return_value='(:version "4.4.1")')
        #with patch.object(subprocess, 'check_output' , return_value='(:version "4.4.1")'):
        #test_patch.return_value = '(:version "4.4.1")'
        print (self.solver._solver_version())
        self.assertTrue(self.solver._solver_version() == Version(major=4, minor=4, patch=1))

    def test_check_solver_newer(self):
        self.solver._received_version = '(:version "4.5.0")'
        self.assertTrue(self.solver._solver_version() > Version(major=4, minor=4, patch=1))

    def test_check_solver_long_format(self):
        self.solver._received_version = '(:version "4.8.6 - build hashcode 78ed71b8de7d")'
        self.assertTrue(self.solver._solver_version() == Version(major=4, minor=8, patch=6))

    def test_check_solver_undefined(self):
        self.solver._received_version = '(:version "78ed71b8de7d")'
        self.assertTrue(

            self.solver._solver_version()
            == Version(major=float("inf"), minor=float("inf"), patch=float("inf"))
        )
        self.assertTrue(self.solver._solver_version() > Version(major=4, minor=4, patch=1))
"""


class ExpressionPropertiesTest(unittest.TestCase):
    _multiprocess_can_split_ = True

    def test_xslotted(self):
        """Test that XSlotted multi inheritance classes uses same amount
        of memory than a single class object with slots
        """

        class Base(object, metaclass=XSlotted, abstract=True):
            __xslots__ = ("t",)
            pass

        class A(Base, abstract=True):
            __xslots__ = ("a",)
            pass

        class B(Base, abstract=True):
            __xslots__ = ("b",)
            pass

        class C(A, B):
            pass

        class X(object):
            __slots__ = ("t", "a", "b")

        c = C()
        c.a = 1
        c.b = 2
        c.t = 10

        x = X()
        x.a = 1
        x.b = 2
        x.t = 20

        self.assertEqual(sys.getsizeof(c), sys.getsizeof(x))

    def test_Expression(self):
        # Used to check if all Expression have test
        checked = set()

        def check(ty: Type, pickle_size=None, sizeof=None, **kwargs):
            x = ty(**kwargs)
            """
            print(
                type(x),
                "\n  Pickle size:",
                len(pickle_dumps(x)),
                "\n  GetSizeOf:",
                sys.getsizeof(x),
                "\n  Slotted:",
                not hasattr(x, "__dict__"),
            )
            """
            self.assertEqual(len(pickle_dumps(x)), pickle_size)
            if sys.version_info[1] == 6:  # Python 3.6
                self.assertEqual(sys.getsizeof(x), sizeof)
            elif sys.version_info[1] == 7:  # Python 3.7
                self.assertEqual(sys.getsizeof(x), sizeof + 8)
            elif sys.version_info[1] >= 8:  # Python 3.8+
                self.assertEqual(sys.getsizeof(x), sizeof - 8)
            self.assertFalse(hasattr(x, "__dict__"))  # slots!
            self.assertTrue(hasattr(x, "_taint"))  # taint!
            checked.add(ty)

        # Can not instantiate an Expression
        for ty in (
            Expression,
            # Constant,  # These are actually tuples of types
            # Variable,
            # Operation,
            BoolOperation,
            BitVecOperation,
            ArrayOperation,
            BitVec,
            Bool,
            Array,
        ):
            self.assertRaises(Exception, ty, ())
            self.assertTrue(hasattr(ty, "__doc__"))
            self.assertTrue(ty.__doc__, ty)
            checked.add(ty)

        # The test numbers are taken from Python 3.6.13 (the oldest supported version)
        # New pythons could use a different number of bytes. Look at the 'check' function
        check(BitVecVariable, size=32, name="name", pickle_size=113, sizeof=64)
        check(BoolVariable, name="name", pickle_size=102, sizeof=56)
        check(
            ArrayVariable,
            index_bits=32,
            value_bits=8,
            index_max=100,
            name="name",
            pickle_size=150,
            sizeof=80,
        )
        check(BitVecConstant, size=32, value=10, pickle_size=109, sizeof=64)
        check(BoolConstant, value=False, pickle_size=97, sizeof=56)

        # But you can instantiate a BoolOr
        x = BoolVariable(name="x")
        y = BoolVariable(name="y")
        z = BoolVariable(name="z")
        check(BoolEqual, a=x, b=y, pickle_size=168, sizeof=56)
        check(BoolAnd, a=x, b=y, pickle_size=166, sizeof=56)
        check(BoolOr, a=x, b=y, pickle_size=165, sizeof=56)
        check(BoolXor, a=x, b=y, pickle_size=166, sizeof=56)
        check(BoolNot, value=x, pickle_size=143, sizeof=56)
        check(BoolITE, cond=z, true=x, false=y, pickle_size=189, sizeof=56)

        bvx = BitVecVariable(size=32, name="bvx")
        bvy = BitVecVariable(size=32, name="bvy")

        check(UnsignedGreaterThan, a=bvx, b=bvy, pickle_size=197, sizeof=56)
        check(GreaterThan, a=bvx, b=bvy, pickle_size=189, sizeof=56)
        check(UnsignedGreaterOrEqual, a=bvx, b=bvy, pickle_size=200, sizeof=56)
        check(GreaterOrEqual, a=bvx, b=bvy, pickle_size=192, sizeof=56)
        check(UnsignedLessThan, a=bvx, b=bvy, pickle_size=194, sizeof=56)
        check(LessThan, a=bvx, b=bvy, pickle_size=186, sizeof=56)
        check(UnsignedLessOrEqual, a=bvx, b=bvy, pickle_size=197, sizeof=56)
        check(LessOrEqual, a=bvx, b=bvy, pickle_size=189, sizeof=56)

        check(BitVecOr, a=bvx, b=bvy, pickle_size=190, sizeof=64)
        check(BitVecXor, a=bvx, b=bvy, pickle_size=191, sizeof=64)
        check(BitVecAnd, a=bvx, b=bvy, pickle_size=191, sizeof=64)
        check(BitVecNot, a=bvx, pickle_size=162, sizeof=64)
        check(BitVecNeg, a=bvx, pickle_size=162, sizeof=64)
        check(BitVecAdd, a=bvx, b=bvy, pickle_size=191, sizeof=64)
        check(BitVecMul, a=bvx, b=bvy, pickle_size=191, sizeof=64)
        check(BitVecSub, a=bvx, b=bvy, pickle_size=191, sizeof=64)
        check(BitVecDiv, a=bvx, b=bvy, pickle_size=191, sizeof=64)
        check(BitVecMod, a=bvx, b=bvy, pickle_size=191, sizeof=64)
        check(BitVecUnsignedDiv, a=bvx, b=bvy, pickle_size=199, sizeof=64)
        check(BitVecRem, a=bvx, b=bvy, pickle_size=191, sizeof=64)
        check(BitVecUnsignedRem, a=bvx, b=bvy, pickle_size=199, sizeof=64)

        check(BitVecShiftLeft, a=bvx, b=bvy, pickle_size=197, sizeof=64)
        check(BitVecShiftRight, a=bvx, b=bvy, pickle_size=198, sizeof=64)
        check(BitVecArithmeticShiftLeft, a=bvx, b=bvy, pickle_size=207, sizeof=64)
        check(BitVecArithmeticShiftRight, a=bvx, b=bvy, pickle_size=208, sizeof=64)

        check(BitVecZeroExtend, operand=bvx, size_dest=122, pickle_size=180, sizeof=72)
        check(BitVecSignExtend, operand=bvx, size_dest=122, pickle_size=180, sizeof=72)
        check(BitVecExtract, operand=bvx, offset=0, size=8, pickle_size=189, sizeof=80)
        check(
            BitVecConcat,
            operands=(bvx, bvy),
            size_dest=(bvx.size + bvy.size),
            pickle_size=194,
            sizeof=64,
        )
        check(
            BitVecITE,
            size=bvx.size,
            condition=x,
            true_value=bvx,
            false_value=bvy,
            pickle_size=231,
            sizeof=64,
        )

        a = ArrayVariable(index_bits=32, value_bits=32, index_max=324, name="name")
        check(ArraySlice, array=a, offset=0, size=10, pickle_size=326, sizeof=136)
        check(ArraySelect, array=a, index=bvx, pickle_size=255, sizeof=64)
        check(ArrayStore, array=a, index=bvx, value=bvy, pickle_size=286, sizeof=120)
        check(ArrayProxy, array=a, default=0, pickle_size=222, sizeof=120)

        def all_subclasses(cls) -> Set[Type]:
            return {cls}.union(
                set(cls.__subclasses__()).union(
                    [s for c in cls.__subclasses__() for s in all_subclasses(c)]
                )
            )

        all_types = all_subclasses(Expression)
        self.assertSetEqual(checked, all_types)


class ExpressionTest(unittest.TestCase):
    _multiprocess_can_split_ = True

    def setUp(self):
        self.solver = Z3Solver.instance()

    def assertItemsEqual(self, a, b):
        # Required for Python3 compatibility
        self.assertEqual(sorted(a), sorted(b))

    def tearDown(self):
        del self.solver

    def test_no_variable_expression_can_be_true(self):
        """
        Tests if solver.can_be_true is correct when the expression has no nodes that subclass
        from Variable (e.g. BitVecConstant)
        """
        x = BitVecConstant(size=32, value=10)
        cs = ConstraintSet()
        self.assertFalse(self.solver.can_be_true(cs, x == False))

    def test_constant_bitvec(self):
        """
        Tests if higher bits are masked out
        """
        x = BitVecConstant(size=32, value=0xFF00000000)
        self.assertTrue(x.value == 0)

    def testBasicAST_001(self):
        """Can't build abstract classes"""
        a = BitVecConstant(size=32, value=100)

        self.assertRaises(TypeError, Expression, ())
        self.assertRaises(TypeError, Constant, 123)
        self.assertRaises(TypeError, Variable, "NAME")
        self.assertRaises(TypeError, Operation, a)

    def testBasicOperation(self):
        """Add"""
        a = BitVecConstant(size=32, value=100)
        b = BitVecVariable(size=32, name="VAR")
        c = a + b
        self.assertIsInstance(c, BitVecAdd)
        self.assertIsInstance(c, Operation)
        self.assertIsInstance(c, Expression)

    def testBasicTaint(self):
        a = BitVecConstant(size=32, value=100, taint=("SOURCE1",))
        b = BitVecConstant(size=32, value=200, taint=("SOURCE2",))
        c = a + b
        self.assertIsInstance(c, BitVecAdd)
        self.assertIsInstance(c, Operation)
        self.assertIsInstance(c, Expression)
        self.assertTrue("SOURCE1" in c.taint)
        self.assertTrue("SOURCE2" in c.taint)

    def testBasicITETaint(self):
        a = BitVecConstant(size=32, value=100, taint=("SOURCE1",))
        b = BitVecConstant(size=32, value=200, taint=("SOURCE2",))
        c = BitVecConstant(size=32, value=300, taint=("SOURCE3",))
        d = BitVecConstant(size=32, value=400, taint=("SOURCE4",))
        x = Operators.ITEBV(32, a > b, c, d)
        self.assertTrue("SOURCE1" in x.taint)
        self.assertTrue("SOURCE2" in x.taint)
        self.assertTrue("SOURCE3" in x.taint)
        self.assertTrue("SOURCE4" in x.taint)

    def test_cs_new_bitvec_invalid_size(self):
        cs = ConstraintSet()
        with self.assertRaises(ValueError) as e:
            cs.new_bitvec(size=0)

        self.assertEqual(str(e.exception), "Bitvec size (0) can't be equal to or less than 0")

        with self.assertRaises(ValueError) as e:
            cs.new_bitvec(size=-23)

        self.assertEqual(str(e.exception), "Bitvec size (-23) can't be equal to or less than 0")

    def testBasicConstraints(self):
        cs = ConstraintSet()
        a = cs.new_bitvec(32)
        b = cs.new_bitvec(32)
        cs.add(a + b > 100)

    def testSolver(self):
        cs = ConstraintSet()
        a = cs.new_bitvec(32)
        b = cs.new_bitvec(32)
        cs.add(a + b > 100)
        self.assertTrue(self.solver.check(cs))

    def testBool1(self):
        cs = ConstraintSet()
        bf = BoolConstant(value=False)
        bt = BoolConstant(value=True)
        cs.add(Operators.AND(bf, bt))
        self.assertFalse(self.solver.check(cs))

    def testBool2(self):
        cs = ConstraintSet()
        bf = BoolConstant(value=False)
        bt = BoolConstant(value=True)
        cs.add(Operators.AND(bf, bt, bt, bt))
        self.assertFalse(self.solver.check(cs))

    def testBool3(self):
        cs = ConstraintSet()
        bf = BoolConstant(value=False)
        bt = BoolConstant(value=True)
        cs.add(Operators.AND(bt, bt, bf, bt))
        self.assertFalse(self.solver.check(cs))

    def testBool4(self):
        cs = ConstraintSet()
        bf = BoolConstant(value=False)
        bt = BoolConstant(value=True)
        cs.add(Operators.OR(True, bf))
        cs.add(Operators.OR(bt, bt, False))
        self.assertTrue(self.solver.check(cs))

    def testBasicArray(self):
        cs = ConstraintSet()
        # make array of 32->8 bits
        array = cs.new_array(32)
        # make free 32bit bitvector
        key = cs.new_bitvec(32)

        # assert that the array is 'A' at key position
        # By default an smtlib can contain any value
        cs.add(array[key] == ord("A"))

        # let's restrict key to be greater than 1000
        cs.add(key.ugt(1000))
        with cs as temp_cs:
            # 1001 position of array can be 'A'
            temp_cs.add(array[1001] == ord("A"))
            self.assertTrue(self.solver.check(temp_cs))

        with cs as temp_cs:
            # 1001 position of array can also be 'B'
            temp_cs.add(array[1001] == ord("B"))
            self.assertTrue(self.solver.check(temp_cs))

        with cs as temp_cs:
            # but if it is 'B' ...
            temp_cs.add(array[1001] == ord("B"))
            # then key can not be 1001
            temp_cs.add(key == 1001)
            self.assertFalse(self.solver.check(temp_cs))

        with cs as temp_cs:
            # If 1001 position is 'B' ...
            temp_cs.add(array[1001] == ord("B"))
            # then key can be 1000 for ex..
            temp_cs.add(key == 1002)
            self.assertTrue(self.solver.check(temp_cs))

    def testBasicArray256(self):
        cs = ConstraintSet()
        # make array of 32->8 bits
        array = cs.new_array(32, value_bits=256)
        # make free 32bit bitvector
        key = cs.new_bitvec(32)

        # assert that the array is 111...111 at key position
        cs.add(array[key] == 11111111111111111111111111111111111111111111)
        # let's restrict key to be greater than 1000
        cs.add(key.ugt(1000))

        with cs as temp_cs:
            # 1001 position of array can be 111...111
            temp_cs.add(array[1001] == 11111111111111111111111111111111111111111111)
            self.assertTrue(self.solver.check(temp_cs))

        with cs as temp_cs:
            # 1001 position of array can also be 222...222
            temp_cs.add(array[1001] == 22222222222222222222222222222222222222222222)
            self.assertTrue(self.solver.check(temp_cs))

        with cs as temp_cs:
            # but if it is 222...222 ...
            temp_cs.add(array[1001] == 22222222222222222222222222222222222222222222)
            # then key can not be 1001
            temp_cs.add(key == 1001)
            self.assertFalse(self.solver.check(temp_cs))

        with cs as temp_cs:
            # If 1001 position is 222...222 ...
            temp_cs.add(array[1001] == 22222222222222222222222222222222222222222222)
            # then key can be 1002 for ex..
            temp_cs.add(key == 1002)
            self.assertTrue(self.solver.check(temp_cs))

    def testBasicArrayStore(self):
        name = "bitarray"
        cs = ConstraintSet()
        # make array of 32->8 bits
        array = cs.new_array(32, name=name)
        # make free 32bit bitvector
        key = cs.new_bitvec(32)

        # assert that the array is 'A' at key position
        array = array.store(key, ord("A"))
        # let's restrict key to be greater than 1000
        cs.add(key.ugt(1000))

        # 1001 position of array can be 'A'
        self.assertTrue(self.solver.can_be_true(cs, array.select(1001) == ord("A")))

        # 1001 position of array can be 'B'
        self.assertTrue(self.solver.can_be_true(cs, array.select(1001) == ord("B")))

        # name is correctly proxied
        self.assertEqual(array.name, name)

        with cs as temp_cs:
            # but if it is 'B' ...
            temp_cs.add(array.select(1001) == ord("B"))
            # then key can not be 1001
            temp_cs.add(key == 1001)
            self.assertFalse(self.solver.check(temp_cs))

        with cs as temp_cs:
            # If 1001 position is 'B' ...
            temp_cs.add(array.select(1001) == ord("B"))
            # then key can be 1002 for ex..
            temp_cs.add(key != 1002)
            self.assertTrue(self.solver.check(temp_cs))

    def testBasicArraySymbIdx(self):
        cs = ConstraintSet()
        array = cs.new_array(index_bits=32, value_bits=32, name="array")
        key = cs.new_bitvec(32, name="key")
        index = cs.new_bitvec(32, name="index")

        array[key] = 1  # Write 1 to a single location

        cs.add(array.get(index, default=0) != 0)  # Constrain index so it selects that location

        cs.add(index != key)
        # key and index are the same there is only one slot in 1
        self.assertFalse(self.solver.check(cs))

    def testBasicArraySymbIdx2(self):
        cs = ConstraintSet()
        array = cs.new_array(index_bits=32, value_bits=32, name="array")
        key = cs.new_bitvec(32, name="key")
        index = cs.new_bitvec(32, name="index")

        array[key] = 1  # Write 1 to a single location
        cs.add(array.get(index, 0) != 0)  # Constrain index so it selects that location
        a_index = self.solver.get_value(cs, index)  # get a concrete solution for index
        cs.add(array.get(a_index, 0) != 0)  # now storage must have something at that location
        cs.add(a_index != index)  # remove it from the solutions

        # It should not be another solution for index
        self.assertFalse(self.solver.check(cs))

    def testBasicArrayConcatSlice(self):
        hw = bytearray(b"Hello world!")
        cs = ConstraintSet()
        # make array of 32->8 bits
        array = cs.new_array(32, index_max=12)

        array = array.write(0, hw)

        self.assertTrue(self.solver.must_be_true(cs, array == hw))

        self.assertTrue(self.solver.must_be_true(cs, array.read(0, 12) == hw))

        self.assertTrue(self.solver.must_be_true(cs, array.read(6, 6) == hw[6:12]))

        self.assertTrue(self.solver.must_be_true(cs, bytearray(b"Hello ") + array.read(6, 6) == hw))

        self.assertTrue(
            self.solver.must_be_true(
                cs, bytearray(b"Hello ") + array.read(6, 5) + bytearray(b"!") == hw
            )
        )

        self.assertTrue(
            self.solver.must_be_true(
                cs,
                array.read(0, 1) + bytearray(b"ello ") + array.read(6, 5) + bytearray(b"!") == hw,
            )
        )

        self.assertTrue(len(array[1:2]) == 1)

        self.assertTrue(len(array[0:12]) == 12)

        results = []
        for c in array[6:11]:
            results.append(c)
        self.assertTrue(len(results) == 5)

    def testBasicArraySlice(self):
        hw = bytearray(b"Hello world!")
        cs = ConstraintSet()
        # make array of 32->8 bits
        array = cs.new_array(32, index_max=12)
        array = array.write(0, hw)
        array_slice = array[0:2]
        self.assertTrue(self.solver.must_be_true(cs, array == hw))
        self.assertTrue(self.solver.must_be_true(cs, array_slice[0] == array[0]))
        self.assertTrue(self.solver.must_be_true(cs, array_slice[0:2][1] == array[1]))
        array_slice[0] = ord("A")
        self.assertTrue(self.solver.must_be_true(cs, array_slice[0] == ord("A")))
        self.assertTrue(self.solver.must_be_true(cs, array_slice[0:2][1] == array[1]))
        self.assertTrue(self.solver.must_be_true(cs, array == hw))

        # Testing some slicing combinations
        self.assertRaises(IndexError, lambda i: translate_to_smtlib(array_slice[0:1000][i]), 1002)
        self.assertTrue(self.solver.must_be_true(cs, array_slice[0:1000][0] == ord("A")))
        self.assertTrue(self.solver.must_be_true(cs, array_slice[0:1000][1] == array[1]))
        self.assertTrue(self.solver.must_be_true(cs, array_slice[0:1000][:2][1] == array[:2][1]))
        self.assertTrue(self.solver.must_be_true(cs, array_slice[0:1000][:2][0] == ord("A")))

    def testBasicArrayProxySymbIdx(self):
        cs = ConstraintSet()
        array = cs.new_array(index_bits=32, value_bits=32, name="array", default=0)
        key = cs.new_bitvec(32, name="key")
        index = cs.new_bitvec(32, name="index")

        array[key] = 1  # Write 1 to a single location
        cs.add(array.get(index) != 0)  # Constrain index so it selects that location
        a_index = self.solver.get_value(cs, index)  # get a concrete solution for index

        cs.add(array.get(a_index) != 0)  # now storage must have something at that location
        cs.add(a_index != index)  # remove it from the solutions
        # It should not be another solution for index
        self.assertFalse(self.solver.check(cs))

    def testBasicArrayProxySymbIdx2(self):
        cs = ConstraintSet()
        array = cs.new_array(index_bits=32, value_bits=32, name="array")
        key = cs.new_bitvec(32, name="key")
        index = cs.new_bitvec(32, name="index")

        array[0] = 1  # Write 1 to first location
        array[key] = 2  # Write 2 to a symbolic (potentially any (potentially 0))location

        solutions = self.solver.get_all_values(cs, array[0])  # get a concrete solution for index
        self.assertItemsEqual(solutions, (1, 2))

        solutions = self.solver.get_all_values(
            cs, array.get(0, 100)
        )  # get a concrete solution for index 0
        self.assertItemsEqual(solutions, (1, 2))

        solutions = self.solver.get_all_values(
            cs, array.get(1, 100)
        )  # get a concrete solution for index 1 (default 100)
        self.assertItemsEqual(solutions, (100, 2))

        self.assertTrue(
            self.solver.can_be_true(cs, array[1] == 12345)
        )  # no default so it can be anything

    def testBasicPickle(self):
        import pickle

        cs = ConstraintSet()

        # make array of 32->8 bits
        array = cs.new_array(32)
        # make free 32bit bitvector
        key = cs.new_bitvec(32)

        # assert that the array is 'A' at key position
        array = array.store(key, ord("A"))
        # let's restrict key to be greater than 1000
        cs.add(key.ugt(1000))
        cs = pickle.loads(pickle_dumps(cs))
        self.assertTrue(self.solver.check(cs))

    def testBitvector_add(self):
        cs = ConstraintSet()
        a = cs.new_bitvec(32)
        b = cs.new_bitvec(32)
        c = cs.new_bitvec(32)
        cs.add(c == a + b)
        cs.add(a == 1)
        cs.add(b == 10)
        self.assertTrue(self.solver.check(cs))
        self.assertEqual(self.solver.get_value(cs, c), 11)

    def testBitvector_add1(self):
        cs = ConstraintSet()
        a = cs.new_bitvec(32)
        b = cs.new_bitvec(32)
        c = cs.new_bitvec(32)
        cs.add(c == a + 10)
        cs.add(a == 1)
        self.assertEqual(self.solver.check(cs), True)
        self.assertEqual(self.solver.get_value(cs, c), 11)

    def testBitvector_add2(self):
        cs = ConstraintSet()
        a = cs.new_bitvec(32)
        b = cs.new_bitvec(32)
        c = cs.new_bitvec(32)
        cs.add(11 == a + 10)
        self.assertTrue(self.solver.check(cs))
        self.assertEqual(self.solver.get_value(cs, a), 1)

    def testBitvector_max(self):
        cs = ConstraintSet()
        a = cs.new_bitvec(32)
        cs.add(a <= 200)
        cs.add(a >= 100)
        self.assertTrue(self.solver.check(cs))
        self.assertEqual(self.solver.minmax(cs, a), (100, 200))
        from manticore import config

        consts = config.get_group("smt")
        consts.optimize = False
        cs = ConstraintSet()
        a = cs.new_bitvec(32)
        cs.add(a <= 200)
        cs.add(a >= 100)
        self.assertTrue(self.solver.check(cs))
        self.assertEqual(self.solver.minmax(cs, a), (100, 200))
        consts.optimize = True

    def testBitvector_max_noop(self):
        from manticore import config

        consts = config.get_group("smt")
        consts.optimize = False
        self.testBitvector_max()
        consts.optimize = True

    def testBitvector_max1(self):
        cs = ConstraintSet()
        a = cs.new_bitvec(32)
        cs.add(a < 200)
        cs.add(a > 100)
        self.assertTrue(self.solver.check(cs))
        self.assertEqual(self.solver.minmax(cs, a), (101, 199))

    def testBitvector_max1_noop(self):
        from manticore import config

        consts = config.get_group("smt")
        consts.optimize = False
        self.testBitvector_max1()
        consts.optimize = True

    def testBool_nonzero(self):
        self.assertTrue(BoolConstant(value=True).__bool__())
        self.assertFalse(BoolConstant(value=False).__bool__())

    def test_visitors(self):
        solver = self.solver
        cs = ConstraintSet()
        arr = cs.new_array(name="MEM")
        a = cs.new_bitvec(32, name="VAR")
        self.assertEqual(get_depth(a), 1)
        cond = Operators.AND(a < 200, a > 100)
        arr[0] = ord("a")
        arr[1] = ord("b")

        self.assertEqual(get_depth(cond), 3)
        self.assertEqual(get_depth(arr[a + 1]), 4)
        self.assertEqual(
            translate_to_smtlib(arr[a + 1]),
            "(select (store (store MEM #x00000000 #x61) #x00000001 #x62) (bvadd VAR #x00000001))",
        )

        arr[3] = arr[a + 1]
        aux = arr[a + Operators.ZEXTEND(arr[a], 32)]

        self.assertEqual(get_depth(aux), 9)
        self.maxDiff = 1500
        self.assertEqual(
            translate_to_smtlib(aux),
            "(select (store (store (store MEM #x00000000 #x61) #x00000001 #x62) #x00000003 (select (store (store MEM #x00000000 #x61) #x00000001 #x62) (bvadd VAR #x00000001))) (bvadd VAR ((_ zero_extend 24) (select (store (store (store MEM #x00000000 #x61) #x00000001 #x62) #x00000003 (select (store (store MEM #x00000000 #x61) #x00000001 #x62) (bvadd VAR #x00000001))) VAR))))",
        )

        values = arr[0:2]
        self.assertEqual(len(values), 2)
        self.assertItemsEqual(solver.get_all_values(cs, values[0]), [ord("a")])
        self.assertItemsEqual(solver.get_all_values(cs, values[1]), [ord("b")])
        arr[1:3] = "cd"

        values = arr[0:3]
        self.assertEqual(len(values), 3)
        self.assertItemsEqual(solver.get_all_values(cs, values[0]), [ord("a")])
        self.assertItemsEqual(solver.get_all_values(cs, values[1]), [ord("c")])
        self.assertItemsEqual(solver.get_all_values(cs, values[2]), [ord("d")])
        self.assertEqual(
            pretty_print(aux, depth=2), "ArraySelect\n  ArrayStore\n    ...\n  BitVecAdd\n    ...\n"
        )
        self.assertEqual(
            pretty_print(Operators.EXTRACT(a, 0, 8), depth=1), "BitVecExtract{0:7}\n  ...\n"
        )
        self.assertEqual(pretty_print(a, depth=2), "VAR\n")

        x = BitVecConstant(size=32, value=100, taint=("important",))
        y = BitVecConstant(size=32, value=200, taint=("stuff",))
        z = constant_folder(x + y)
        self.assertItemsEqual(z.taint, ("important", "stuff"))
        self.assertEqual(z.value, 300)

        self.assertRaises(Exception, translate_to_smtlib, 1)

        self.assertEqual(translate_to_smtlib(simplify(Operators.ZEXTEND(a, 32))), "VAR")
        self.assertEqual(
            translate_to_smtlib(simplify(Operators.EXTRACT(Operators.EXTRACT(a, 0, 8), 0, 8))),
            "((_ extract 7 0) VAR)",
        )

    def test_arithmetic_simplify(self):
        cs = ConstraintSet()
        arr = cs.new_array(name="MEM")
        a = cs.new_bitvec(32, name="VARA")
        b = cs.new_bitvec(32, name="VARB")
        c = a * 2 + b
        self.assertEqual(translate_to_smtlib(c), "(bvadd (bvmul VARA #x00000002) VARB)")
        self.assertEqual(
            translate_to_smtlib((c + 4) - 4),
            "(bvsub (bvadd (bvadd (bvmul VARA #x00000002) VARB) #x00000004) #x00000004)",
        )

        d = c + 4
        s = arithmetic_simplify(d - c)
        self.assertIsInstance(s, Constant)
        self.assertEqual(s.value, 4)
        # size = arithmetic_simplify(size

        cs2 = ConstraintSet()
        exp = cs2.new_bitvec(32)
        exp |= 0
        exp &= 1
        exp |= 0
        self.assertEqual(get_depth(exp), 4)
        self.assertEqual(
            translate_to_smtlib(exp),
            "(bvor (bvand (bvor BITVEC #x00000000) #x00000001) #x00000000)",
        )
        exp = arithmetic_simplify(exp)
        self.assertTrue(get_depth(exp) < 4)
        self.assertEqual(translate_to_smtlib(exp), "(bvand BITVEC #x00000001)")

    def test_arithmetic_simplify_extract(self):
        cs = ConstraintSet()
        arr = cs.new_array(name="MEM")
        a = cs.new_bitvec(32, name="VARA")
        b = Operators.CONCAT(
            32,
            Operators.EXTRACT(a, 24, 8),
            Operators.EXTRACT(a, 16, 8),
            Operators.EXTRACT(a, 8, 8),
            Operators.EXTRACT(a, 0, 8),
        )
        self.assertEqual(
            translate_to_smtlib(b),
            "(concat ((_ extract 31 24) VARA) ((_ extract 23 16) VARA) ((_ extract 15 8) VARA) ((_ extract 7 0) VARA))",
        )
        self.assertEqual(translate_to_smtlib(simplify(b)), "VARA")

        c = Operators.CONCAT(16, Operators.EXTRACT(a, 16, 8), Operators.EXTRACT(a, 8, 8))
        self.assertEqual(
            translate_to_smtlib(c), "(concat ((_ extract 23 16) VARA) ((_ extract 15 8) VARA))"
        )
        self.assertEqual(translate_to_smtlib(simplify(c)), "((_ extract 23 8) VARA)")

    def test_constant_folding_extract(self):
        cs = ConstraintSet()
        x = BitVecConstant(size=32, value=0xAB123456, taint=("important",))
        z = constant_folder(BitVecExtract(operand=x, offset=8, size=16))
        self.assertItemsEqual(z.taint, ("important",))
        self.assertEqual(z.value, 0x1234)

    def test_arithmetic_simplify_udiv(self):
        cs = ConstraintSet()
        a = cs.new_bitvec(32, name="VARA")
        b = a + Operators.UDIV(BitVecConstant(size=32, value=0), BitVecConstant(size=32, value=2))
        self.assertEqual(translate_to_smtlib(b), "(bvadd VARA (bvudiv #x00000000 #x00000002))")
        self.assertEqual(translate_to_smtlib(simplify(b)), "VARA")

        c = a + Operators.UDIV(BitVecConstant(size=32, value=2), BitVecConstant(size=32, value=2))
        self.assertEqual(translate_to_smtlib(c), "(bvadd VARA (bvudiv #x00000002 #x00000002))")
        self.assertEqual(translate_to_smtlib(simplify(c)), "(bvadd VARA #x00000001)")

    def test_constant_folding_udiv(self):
        cs = ConstraintSet()
        x = BitVecConstant(size=32, value=0xFFFFFFFF, taint=("important",))
        y = BitVecConstant(size=32, value=2, taint=("stuff",))
        z = constant_folder(x.udiv(y))
        self.assertItemsEqual(z.taint, ("important", "stuff"))
        self.assertEqual(z.value, 0x7FFFFFFF)

    def test_simplify_OR(self):
        cs = ConstraintSet()
        bf = BoolConstant(value=False)
        bt = BoolConstant(value=True)
        var = cs.new_bool()
        cs.add(simplify(Operators.OR(var, var)) == var)
        cs.add(simplify(Operators.OR(var, bt)) == bt)
        self.assertTrue(self.solver.check(cs))

    def test_simplify_SUB(self):
        cs = ConstraintSet()
        var = cs.new_bitvec(size=32)
        cs.add(simplify(var - var) == 0)
        cs.add(simplify(var - 0) == var)
        self.assertTrue(self.solver.check(cs))

    def testBasicReplace(self):
        """Add"""
        a = BitVecConstant(size=32, value=100)
        b1 = BitVecVariable(size=32, name="VAR1")
        b2 = BitVecVariable(size=32, name="VAR2")

        c = a + b1

        x = replace(c, {b1: b2})
        self.assertEqual(translate_to_smtlib(x), "(bvadd #x00000064 VAR2)")

    def testBasicMigration(self):
        solver = self.solver
        cs1 = ConstraintSet()
        cs2 = ConstraintSet()
        var1 = cs1.new_bitvec(32, "var")
        var2 = cs2.new_bitvec(32, "var")
        cs1.add(Operators.ULT(var1, 3))  # var1 can be 0, 1, 2

        # make a migration map dict
        migration_map1 = {}

        # this expression is composed with variables of both cs
        expression = var1 > var2
        migrated_expression = cs1.migrate(expression, migration_map1)
        cs1.add(migrated_expression)

        expression = var2 > 0
        migrated_expression = cs1.migrate(expression, migration_map1)
        cs1.add(migrated_expression)

        self.assertItemsEqual(solver.get_all_values(cs1, var1), [2])  # should only be [2]

    def test_SAR(self):
        solver = self.solver
        A = 0xBADF00D
        for B in range(32):
            cs = ConstraintSet()
            a = cs.new_bitvec(32)
            b = cs.new_bitvec(32)
            c = cs.new_bitvec(32)

            cs.add(c == Operators.SAR(32, a, b))
            cs.add(a == A)
            cs.add(b == B)

            self.assertTrue(solver.check(cs))
            self.assertEqual(solver.get_value(cs, c), Operators.SAR(32, A, B))

    def test_ConstraintsForking(self):
        solver = self.solver
        import pickle

        cs = ConstraintSet()
        # make free 32bit bitvectors
        x = cs.new_bitvec(8)
        y = cs.new_bitvec(8)

        # linear relation
        # cs.add(x+y*5 == 0)

        # Fork and divide in quadrants

        saved_up = None
        saved_up_right = None
        saved_up_left = None
        saved_down = None
        saved_down_right = None
        saved_down_left = None

        with cs as cs_up:
            cs_up.add(y.uge(0x80))
            self.assertItemsEqual(solver.get_all_values(cs_up, x), range(0x0, 0x100))
            self.assertItemsEqual(solver.get_all_values(cs_up, y), range(0x80, 0x100))

            saved_up = pickle_dumps((x, y, cs_up))

            self.assertItemsEqual(solver.get_all_values(cs_up, x), range(0x0, 0x100))
            self.assertItemsEqual(solver.get_all_values(cs_up, y), range(0x80, 0x100))

            with cs_up as cs_up_right:
                cs_up_right.add(x.uge(0x80))
                saved_up_right = pickle_dumps((x, y, cs_up_right))
                self.assertItemsEqual(solver.get_all_values(cs_up_right, x), range(0x80, 0x100))
                self.assertItemsEqual(solver.get_all_values(cs_up_right, y), range(0x80, 0x100))

            self.assertItemsEqual(solver.get_all_values(cs_up, x), range(0x0, 0x100))
            self.assertItemsEqual(solver.get_all_values(cs_up, y), range(0x80, 0x100))

            with cs_up as cs_up_left:
                cs_up_left.add(x.ult(0x80))
                saved_up_left = pickle_dumps((x, y, cs_up_left))
                self.assertItemsEqual(solver.get_all_values(cs_up_left, x), range(0, 0x80))
                self.assertItemsEqual(solver.get_all_values(cs_up_left, y), range(0x80, 0x100))

            self.assertItemsEqual(solver.get_all_values(cs_up, x), range(0x0, 0x100))
            self.assertItemsEqual(solver.get_all_values(cs_up, y), range(0x80, 0x100))

        with cs as cs_down:
            cs_down.add(y.ult(0x80))

            self.assertItemsEqual(solver.get_all_values(cs_down, x), range(0x0, 0x100))
            self.assertItemsEqual(solver.get_all_values(cs_down, y), range(0, 0x80))

            saved_down = pickle_dumps((x, y, cs_down))

            self.assertItemsEqual(solver.get_all_values(cs_down, x), range(0x0, 0x100))
            self.assertItemsEqual(solver.get_all_values(cs_down, y), range(0, 0x80))

            with cs_down as cs_down_right:
                cs_down_right.add(x.uge(0x80))
                saved_down_right = pickle_dumps((x, y, cs_down_right))
                self.assertItemsEqual(solver.get_all_values(cs_down_right, x), range(0x80, 0x100))
                self.assertItemsEqual(solver.get_all_values(cs_down_right, y), range(0, 0x80))

            self.assertItemsEqual(solver.get_all_values(cs_down, x), range(0x0, 0x100))
            self.assertItemsEqual(solver.get_all_values(cs_down, y), range(0, 0x80))

            with cs_down as cs_down_left:
                cs_down_left.add(x.ult(0x80))
                saved_down_left = pickle_dumps((x, y, cs_down_left))
                self.assertItemsEqual(solver.get_all_values(cs_down_left, x), range(0, 0x80))
                self.assertItemsEqual(solver.get_all_values(cs_down_left, y), range(0, 0x80))

            self.assertItemsEqual(solver.get_all_values(cs_down, x), range(0x0, 0x100))
            self.assertItemsEqual(solver.get_all_values(cs_down, y), range(0, 0x80))

            x, y, cs_up = pickle.loads(saved_up)
            self.assertItemsEqual(solver.get_all_values(cs_up, x), range(0x0, 0x100))
            self.assertItemsEqual(solver.get_all_values(cs_up, y), range(0x80, 0x100))

            x, y, cs_up_right = pickle.loads(saved_up_right)
            self.assertItemsEqual(solver.get_all_values(cs_up_right, x), range(0x80, 0x100))
            self.assertItemsEqual(solver.get_all_values(cs_up_right, y), range(0x80, 0x100))

            x, y, cs_up_left = pickle.loads(saved_up_left)
            self.assertItemsEqual(solver.get_all_values(cs_up_left, x), range(0x00, 0x80))
            self.assertItemsEqual(solver.get_all_values(cs_up_left, y), range(0x80, 0x100))

            x, y, cs_down = pickle.loads(saved_down)
            self.assertItemsEqual(solver.get_all_values(cs_down, x), range(0x0, 0x100))
            self.assertItemsEqual(solver.get_all_values(cs_down, y), range(0x0, 0x80))

            x, y, cs_down_right = pickle.loads(saved_down_right)
            self.assertItemsEqual(solver.get_all_values(cs_down_right, x), range(0x80, 0x100))
            self.assertItemsEqual(solver.get_all_values(cs_down_right, y), range(0x00, 0x80))

            x, y, cs_down_left = pickle.loads(saved_down_left)
            self.assertItemsEqual(solver.get_all_values(cs_down_left, x), range(0x00, 0x80))
            self.assertItemsEqual(solver.get_all_values(cs_down_left, y), range(0x00, 0x80))

    def test_ORD(self):
        solver = self.solver
        cs = ConstraintSet()
        a = cs.new_bitvec(8)
        cs.add(Operators.ORD(a) == Operators.ORD("Z"))

        self.assertTrue(solver.check(cs))
        self.assertEqual(solver.get_value(cs, a), ord("Z"))

    def test_ORD_proper_extract(self):
        solver = self.solver
        cs = ConstraintSet()
        a = cs.new_bitvec(32)
        cs.add(Operators.ORD(a) == Operators.ORD("\xff"))

        self.assertTrue(solver.check(cs))
        self.assertEqual(solver.get_value(cs, a), ord("\xff"))

    def test_CHR(self):
        solver = self.solver
        cs = ConstraintSet()
        a = cs.new_bitvec(8)
        cs.add(Operators.CHR(a) == Operators.CHR(0x41))

        self.assertTrue(solver.check(cs))
        self.assertEqual(solver.get_value(cs, a), 0x41)

    def test_CONCAT(self):
        solver = self.solver
        cs = ConstraintSet()
        a = cs.new_bitvec(16)
        b = cs.new_bitvec(8)
        c = cs.new_bitvec(8)

        cs.add(b == 0x41)
        cs.add(c == 0x42)
        cs.add(a == Operators.CONCAT(a.size, b, c))

        self.assertTrue(solver.check(cs))
        self.assertEqual(solver.get_value(cs, a), Operators.CONCAT(a.size, 0x41, 0x42))

    def test_ITEBV_1(self):
        solver = self.solver
        cs = ConstraintSet()
        a = cs.new_bitvec(8)
        b = cs.new_bitvec(8)
        c = cs.new_bitvec(8)

        cs.add(b == 0x41)
        cs.add(c == 0x42)
        cs.add(a == Operators.ITEBV(8, b == c, b, c))

        self.assertTrue(solver.check(cs))
        self.assertEqual(solver.get_value(cs, a), 0x42)

    def test_ITEBV_2(self):
        solver = self.solver
        cs = ConstraintSet()
        a = cs.new_bitvec(8)
        b = cs.new_bitvec(8)
        c = cs.new_bitvec(8)

        cs.add(b == 0x44)
        cs.add(c == 0x44)
        cs.add(a == Operators.ITEBV(8, b == c, b, c))

        self.assertTrue(solver.check(cs))
        self.assertEqual(solver.get_value(cs, a), 0x44)

    def test_ITE(self):
        solver = self.solver
        cs = ConstraintSet()
        a = cs.new_bool()
        b = cs.new_bool()
        c = cs.new_bool()

        cs.add(b == True)
        cs.add(c == False)
        cs.add(a == Operators.ITE(b == c, b, c))

        self.assertTrue(solver.check(cs))
        self.assertEqual(solver.get_value(cs, a), False)

    def test_UREM(self):
        solver = self.solver
        cs = ConstraintSet()
        a = cs.new_bitvec(8)
        b = cs.new_bitvec(8)
        c = cs.new_bitvec(8)
        d = cs.new_bitvec(8)

        cs.add(b == 0x86)  # 134
        cs.add(c == 0x11)  # 17
        cs.add(a == Operators.UREM(b, c))
        cs.add(d == b.urem(c))
        cs.add(a == d)

        self.assertTrue(solver.check(cs))
        self.assertEqual(solver.get_value(cs, a), 0xF)

    def test_SREM(self):
        solver = self.solver
        cs = ConstraintSet()
        a = cs.new_bitvec(8)
        b = cs.new_bitvec(8)
        c = cs.new_bitvec(8)
        d = cs.new_bitvec(8)

        cs.add(b == 0x86)  # -122
        cs.add(c == 0x11)  # 17
        cs.add(a == Operators.SREM(b, c))
        cs.add(d == b.srem(c))
        cs.add(a == d)

        self.assertTrue(solver.check(cs))
        self.assertEqual(solver.get_value(cs, a), -3 & 0xFF)

    def test_UDIV(self):
        solver = self.solver
        cs = ConstraintSet()
        a = cs.new_bitvec(8)
        b = cs.new_bitvec(8)
        c = cs.new_bitvec(8)
        d = cs.new_bitvec(8)

        cs.add(b == 0x86)  # 134
        cs.add(c == 0x11)  # 17
        cs.add(a == Operators.UDIV(b, c))
        cs.add(d == b.udiv(c))
        cs.add(a == d)

        self.assertTrue(solver.check(cs))
        self.assertEqual(solver.get_value(cs, a), 7)

    def test_SDIV(self):
        solver = self.solver
        cs = ConstraintSet()
        a = cs.new_bitvec(8)
        b = cs.new_bitvec(8)
        c = cs.new_bitvec(8)
        d = cs.new_bitvec(8)

        cs.add(b == 0x86)  # -122
        cs.add(c == 0x11)  # 17
        cs.add(a == Operators.SDIV(b, c))
        cs.add(d == (b // c))
        cs.add(a == d)
        self.assertTrue(solver.check(cs))
        self.assertEqual(solver.get_value(cs, a), -7 & 0xFF)

    def test_ULE(self):
        solver = self.solver
        cs = ConstraintSet()
        a = cs.new_bitvec(8)
        b = cs.new_bitvec(8)
        c = cs.new_bitvec(8)

        cs.add(a == 0x1)  # 1
        cs.add(b == 0x86)  # -122
        cs.add(c == 0x11)  # 17
        self.assertTrue(solver.must_be_true(cs, Operators.ULE(a, b)))
        self.assertTrue(solver.must_be_true(cs, Operators.ULE(a, c)))
        self.assertTrue(solver.must_be_true(cs, Operators.ULE(c, b)))
        self.assertTrue(solver.must_be_true(cs, Operators.ULE(a, 0xF2)))
        self.assertTrue(solver.must_be_true(cs, Operators.ULE(b, 0x99)))
        self.assertTrue(solver.must_be_true(cs, Operators.ULE(c, 0x12)))
        self.assertTrue(solver.must_be_true(cs, Operators.ULE(3, 0xF2)))
        self.assertTrue(solver.must_be_true(cs, Operators.ULE(3, 3)))
        self.assertTrue(solver.must_be_true(cs, Operators.ULE(1, a)))
        self.assertTrue(solver.must_be_true(cs, Operators.ULE(0x85, b)))
        self.assertTrue(solver.must_be_true(cs, Operators.ULE(0x10, c)))

    def test_ULT(self):
        solver = self.solver
        cs = ConstraintSet()
        a = cs.new_bitvec(8)
        b = cs.new_bitvec(8)
        c = cs.new_bitvec(8)

        cs.add(a == 0x1)  # 1
        cs.add(b == 0x86)  # -122
        cs.add(c == 0x11)  # 17
        self.assertTrue(solver.must_be_true(cs, Operators.ULT(a, b)))
        self.assertTrue(solver.must_be_true(cs, Operators.ULT(a, c)))
        self.assertTrue(solver.must_be_true(cs, Operators.ULT(c, b)))
        self.assertTrue(solver.must_be_true(cs, Operators.ULT(a, 0xF2)))
        self.assertTrue(solver.must_be_true(cs, Operators.ULT(b, 0x99)))
        self.assertTrue(solver.must_be_true(cs, Operators.ULT(c, 0x12)))
        self.assertTrue(solver.must_be_true(cs, Operators.ULT(3, 0xF2)))
        self.assertTrue(solver.must_be_true(cs, Operators.ULT(3, 4)))
        self.assertTrue(solver.must_be_true(cs, Operators.ULT(0, a)))
        self.assertTrue(solver.must_be_true(cs, Operators.ULT(0x85, b)))
        self.assertTrue(solver.must_be_true(cs, Operators.ULT(0x10, c)))

    def test_NOT(self):
        solver = self.solver
        cs = ConstraintSet()
        a = cs.new_bitvec(8)
        b = cs.new_bitvec(8)

        cs.add(a == 0x1)  # 1
        cs.add(b == 0x86)  # -122
        self.assertTrue(solver.must_be_true(cs, Operators.NOT(False)))
        self.assertTrue(solver.must_be_true(cs, Operators.NOT(a == b)))

    def testRelated(self):
        cs = ConstraintSet()
        aa1 = cs.new_bool(name="AA1")
        aa2 = cs.new_bool(name="AA2")
        bb1 = cs.new_bool(name="BB1")
        bb2 = cs.new_bool(name="BB2")
        cs.add(Operators.OR(aa1, aa2))
        cs.add(Operators.OR(bb1, bb2))
        self.assertTrue(self.solver.check(cs))
        # No BB variables related to AA
        self.assertNotIn("BB", cs.related_to(aa1).to_string())
        self.assertNotIn("BB", cs.related_to(aa2).to_string())
        self.assertNotIn("BB", cs.related_to(aa1 == aa2).to_string())
        self.assertNotIn("BB", cs.related_to(aa1 == False).to_string())
        # No AA variables related to BB
        self.assertNotIn("AA", cs.related_to(bb1).to_string())
        self.assertNotIn("AA", cs.related_to(bb2).to_string())
        self.assertNotIn("AA", cs.related_to(bb1 == bb2).to_string())
        self.assertNotIn("AA", cs.related_to(bb1 == False).to_string())

        # Nothing is related to tautologies?
        self.assertEqual("", cs.related_to(simplify(bb1 == bb1)).to_string())

        # But if the tautollogy can not get simplified we have to ask the solver
        # and send in all the other stuff
        self.assertNotIn("AA", cs.related_to(bb1 == bb1).to_string())

    def test_API(self):
        """
        As we've split up the Constant, Variable, and Operation classes to avoid using multiple inheritance,
        this test ensures that their expected properties are still present on their former subclasses. Doesn't
        check the types or behavior, but hopefully will at least help avoid footguns related to defining new
        Constant/Variable/Operation types in the future.
        """
        for cls in Constant:
            attrs = ["value"]
            for attr in attrs:
                self.assertTrue(hasattr(cls, attr), f"{cls.__name__} is missing attribute {attr}")

        for cls in Variable:
            attrs = ["name", "declaration", "__copy__", "__deepcopy__"]
            for attr in attrs:
                self.assertTrue(hasattr(cls, attr), f"{cls.__name__} is missing attribute {attr}")

        for cls in Operation:
            attrs = ["operands"]
            for attr in attrs:
                self.assertTrue(hasattr(cls, attr), f"{cls.__name__} is missing attribute {attr}")

    def test_signed_unsigned_LT_simple(self):
        cs = ConstraintSet()
        a = cs.new_bitvec(32)
        b = cs.new_bitvec(32)

        cs.add(a == 0x1)
        cs.add(b == 0x80000000)

        lt = b < a
        ult = b.ult(a)

        self.assertFalse(self.solver.can_be_true(cs, ult))
        self.assertTrue(self.solver.must_be_true(cs, lt))

    def test_signed_unsigned_LT_complex(self):
        mask = (1 << 32) - 1

        cs = ConstraintSet()
        _a = cs.new_bitvec(32)
        _b = cs.new_bitvec(32)

        cs.add(_a == 0x1)
        cs.add(_b == (0x80000000 - 1))

        a = _a & mask
        b = (_b + 1) & mask

        lt = b < a
        ult = b.ult(a)

        self.assertFalse(self.solver.can_be_true(cs, ult))
        self.assertTrue(self.solver.must_be_true(cs, lt))


class ExpressionTestYices(ExpressionTest):
    def setUp(self):
        self.solver = YicesSolver.instance()


class ExpressionTestCVC4(ExpressionTest):
    def setUp(self):
        self.solver = CVC4Solver.instance()


class ExpressionTestBoolector(ExpressionTest):
    def setUp(self):
        self.solver = BoolectorSolver.instance()


class ExpressionTestPortfolio(ExpressionTest):
    def setUp(self):
        self.solver = PortfolioSolver.instance()


if __name__ == "__main__":
    unittest.main()
