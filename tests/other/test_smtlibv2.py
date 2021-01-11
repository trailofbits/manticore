import unittest
import os
import sys
import pickle
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
)
from manticore.core.smtlib.solver import Z3Solver, YicesSolver, CVC4Solver, SelectedSolver
from manticore.core.smtlib.expression import *
from manticore.utils.helpers import pickle_dumps
from manticore import config

# logging.basicConfig(filename = "test.log",
#                format = "%(asctime)s: %(name)s:%(levelname)s: %(message)s",
#                level = logging.DEBUG)

DIRPATH = os.path.dirname(__file__)


class ExpressionTestNew(unittest.TestCase):
    _multiprocess_can_split_ = True

    def setUp(self):
        self.solver = Z3Solver.instance()

    def assertItemsEqual(self, a, b):
        # Required for Python3 compatibility
        self.assertEqual(sorted(a), sorted(b))

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
        c.t = 10

        c.b = 2
        c.t = 10

        x = X()
        x.a = 1
        x.b = 2
        x.t = 20

        self.assertEqual(sys.getsizeof(c), sys.getsizeof(x))

    def test_BitVec_ops(self):
        a = BitVecVariable(size=32, name="BV")
        b = BitVecVariable(size=32, name="BV1")
        c = BitVecVariable(size=32, name="BV2")
        x = BitVecConstant(size=32, value=100, taint=("T",))
        z = (b + 1) % b < a * x / c - 5
        self.assertSetEqual(z.taint, set(("T",)))
        self.assertEqual(
            translate_to_smtlib(z),
            "(bvslt (bvsmod (bvadd BV1 #x00000001) BV1) (bvsub (bvsdiv (bvmul BV #x00000064) BV2) #x00000005))",
        )
        z = (1 + b) / b <= a - x * 5 + c
        self.assertSetEqual(z.taint, set(("T",)))
        self.assertEqual(
            translate_to_smtlib(z),
            "(bvsle (bvsdiv (bvadd #x00000001 BV1) BV1) (bvadd (bvsub BV (bvmul #x00000064 #x00000005)) BV2))",
        )

    def test_ConstantArrayBitVec(self):
        c = ArrayConstant(index_size=32, value_size=8, value=b"ABCDE")
        self.assertEqual(c[0], ord("A"))
        self.assertEqual(c[1], ord("B"))
        self.assertEqual(c[2], ord("C"))
        self.assertEqual(c[3], ord("D"))
        self.assertEqual(c[4], ord("E"))
        self.assertRaises(IndexError, c.__getitem__, 5)

    def test_ConstantArrayBitVec2(self):
        c = MutableArray(ArrayVariable(index_size=32, value_size=8, length=5, name="ARR"))
        c[1] = 10
        c[2] = 20
        c[3] = 30
        self.assertEqual(c[1], 10)
        self.assertEqual(c[2], 20)
        self.assertEqual(c[3], 30)
        c[2] = 100
        self.assertEqual(c[2], 100)

    def test_ArrayDefault3(self):
        c = MutableArray(
            ArrayVariable(index_size=32, value_size=8, length=5, default=0, name="ARR")
        )
        self.assertEqual(c[1], 0)
        self.assertEqual(c[2], 0)
        self.assertEqual(c[3], 0)

        c[1] = 10
        c[3] = 30
        self.assertEqual(c[1], 10)
        self.assertEqual(c[2], 0)
        self.assertEqual(c[3], 30)

    def test_ArrayDefault4(self):
        cs = ConstraintSet()
        a = MutableArray(cs.new_array(index_size=32, value_size=8, length=4, default=0, name="ARR"))
        i = cs.new_bitvec(size=a.index_size)
        SelectedSolver.instance().must_be_true(cs, 0 == a.default)
        SelectedSolver.instance().must_be_true(cs, a[i] == a.default)
        cs.add(i == 2)
        SelectedSolver.instance().must_be_true(cs, 0 == a.default)
        SelectedSolver.instance().must_be_true(cs, a[i] == a.default)

        b = a[:]
        i = cs.new_bitvec(size=a.index_size)
        SelectedSolver.instance().must_be_true(cs, 0 == b.default)
        SelectedSolver.instance().must_be_true(cs, b[i] == b.default)

        a[1] = 10
        a[2] = 20
        a[3] = 30
        # a := 0 10 20 30 0 0 x x x x      (x undefined)
        SelectedSolver.instance().must_be_true(cs, a.default == 0)
        SelectedSolver.instance().must_be_true(cs, a[0] == 0)
        SelectedSolver.instance().must_be_true(cs, a[1] == 10)
        SelectedSolver.instance().must_be_true(cs, a[2] == 20)
        SelectedSolver.instance().must_be_true(cs, a[3] == 30)
        # SelectedSolver.instance().must_be_true(cs, a[4] == 0) #undefined!

        b = a[:]
        # b := 0 10 20 30 0 0 x x x x      (x undefined)
        SelectedSolver.instance().must_be_true(cs, b.default == 0)
        SelectedSolver.instance().must_be_true(cs, b[0] == 0)
        SelectedSolver.instance().must_be_true(cs, b[1] == 10)
        SelectedSolver.instance().must_be_true(cs, b[2] == 20)
        SelectedSolver.instance().must_be_true(cs, b[3] == 30)

    def test_Expression(self):
        # Used to check if all Expression have test
        checked = set()

        def check(ty, pickle_size=None, sizeof=None, **kwargs):
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
            # self.assertEqual(len(pickle_dumps(x)), pickle_size)
            # self.assertEqual(sys.getsizeof(x), sizeof)
            # The test numbers are taken from Python 3.8.5 older pythons use 8 more bytes sometimes
            self.assertLessEqual(sys.getsizeof(x), sizeof + 8)
            self.assertFalse(hasattr(x, "__dict__"))  # slots!
            self.assertTrue(hasattr(x, "_taint"))  # taint!
            checked.add(ty)

        # Can not instantiate an Expression
        for ty in (
            Expression,
            Constant,
            Variable,
            Operation,
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

        check(BitVecVariable, size=32, name="name", pickle_size=111, sizeof=56)
        check(BoolVariable, name="name", pickle_size=99, sizeof=48)
        check(
            ArrayVariable,
            index_size=32,
            value_size=8,
            length=100,
            name="name",
            pickle_size=156,
            sizeof=80,
        )
        check(BitVecConstant, size=32, value=10, pickle_size=107, sizeof=56)
        check(BoolConstant, value=False, pickle_size=94, sizeof=48)

        # TODO! But you can instantiate an ArraConstant
        """
        x = ArrayConstant(index_size=32, value_size=8, b"AAAAAAAAAAAAAAA")
        self.assertLessEqual(len(pickle_dumps(x)), 76) #master 71
        self.assertLessEqual(sys.getsizeof(x), 64) #master 56
        self.assertFalse(hasattr(x, '__dict__')) #slots!
        """

        # But you can instantiate a BoolOr
        x = BoolVariable(name="x")
        y = BoolVariable(name="y")
        z = BoolVariable(name="z")
        check(BoolEqual, operanda=x, operandb=y, pickle_size=159, sizeof=48)
        check(BoolAnd, operanda=x, operandb=y, pickle_size=157, sizeof=48)
        check(BoolOr, operanda=x, operandb=y, pickle_size=156, sizeof=48)
        check(BoolXor, operanda=x, operandb=y, pickle_size=157, sizeof=48)
        check(BoolNot, operand=x, pickle_size=137, sizeof=48)
        check(BoolITE, cond=z, true=x, false=y, pickle_size=130, sizeof=48)

        bvx = BitVecVariable(size=32, name="bvx")
        bvy = BitVecVariable(size=32, name="bvy")

        check(BoolUnsignedGreaterThan, operanda=bvx, operandb=bvy, pickle_size=142, sizeof=48)
        check(BoolGreaterThan, operanda=bvx, operandb=bvy, pickle_size=134, sizeof=48)
        check(
            BoolUnsignedGreaterOrEqualThan, operanda=bvx, operandb=bvy, pickle_size=149, sizeof=48
        )
        check(BoolGreaterOrEqualThan, operanda=bvx, operandb=bvy, pickle_size=141, sizeof=48)
        check(BoolUnsignedLessThan, operanda=bvx, operandb=bvy, pickle_size=139, sizeof=48)
        check(BoolLessThan, operanda=bvx, operandb=bvy, pickle_size=131, sizeof=48)
        check(BoolUnsignedLessOrEqualThan, operanda=bvx, operandb=bvy, pickle_size=146, sizeof=48)
        check(BoolLessOrEqualThan, operanda=bvx, operandb=bvy, pickle_size=138, sizeof=48)

        check(BitVecOr, operanda=bvx, operandb=bvy, pickle_size=129, sizeof=56)
        check(BitVecXor, operanda=bvx, operandb=bvy, pickle_size=130, sizeof=56)
        check(BitVecAnd, operanda=bvx, operandb=bvy, pickle_size=130, sizeof=56)
        check(BitVecNot, operanda=bvx, pickle_size=112, sizeof=56)
        check(BitVecNeg, operanda=bvx, pickle_size=112, sizeof=56)
        check(BitVecAdd, operanda=bvx, operandb=bvy, pickle_size=130, sizeof=56)
        check(BitVecMul, operanda=bvx, operandb=bvy, pickle_size=130, sizeof=56)
        check(BitVecSub, operanda=bvx, operandb=bvy, pickle_size=130, sizeof=56)
        check(BitVecDiv, operanda=bvx, operandb=bvy, pickle_size=130, sizeof=56)
        check(BitVecMod, operanda=bvx, operandb=bvy, pickle_size=130, sizeof=56)
        check(BitVecUnsignedDiv, operanda=bvx, operandb=bvy, pickle_size=138, sizeof=56)
        check(BitVecRem, operanda=bvx, operandb=bvy, pickle_size=130, sizeof=56)
        check(BitVecUnsignedRem, operanda=bvx, operandb=bvy, pickle_size=138, sizeof=56)

        check(BitVecShiftLeft, operanda=bvx, operandb=bvy, pickle_size=136, sizeof=56)
        check(BitVecShiftRight, operanda=bvx, operandb=bvy, pickle_size=137, sizeof=56)
        check(BitVecArithmeticShiftLeft, operanda=bvx, operandb=bvy, pickle_size=146, sizeof=56)
        check(BitVecArithmeticShiftRight, operanda=bvx, operandb=bvy, pickle_size=147, sizeof=56)

        check(BitVecZeroExtend, operand=bvx, size=122, pickle_size=119, sizeof=56)
        check(BitVecSignExtend, operand=bvx, size=122, pickle_size=119, sizeof=56)
        check(BitVecExtract, operand=bvx, offset=0, size=8, pickle_size=119, sizeof=64)
        check(BitVecConcat, operands=(bvx, bvy), pickle_size=133, sizeof=56)
        check(BitVecITE, condition=x, true_value=bvx, false_value=bvy, pickle_size=161, sizeof=56)

        a = ArrayVariable(index_size=32, value_size=32, length=324, name="name")
        check(ArrayConstant, index_size=32, value_size=8, value=b"A", pickle_size=136, sizeof=64)
        check(ArraySlice, array=a, offset=0, size=10, pickle_size=136, sizeof=48)
        check(ArraySelect, array=a, index=bvx, pickle_size=161, sizeof=56)
        check(ArrayStore, array=a, index=bvx, value=bvy, pickle_size=188, sizeof=80)

        def all_subclasses(cls):
            return set((Expression,)).union(
                set(cls.__subclasses__()).union(
                    [s for c in cls.__subclasses__() for s in all_subclasses(c)]
                )
            )

        all_types = all_subclasses(Expression)
        self.assertSetEqual(checked, all_types)

    def test_Expression_BitVecOp(self):
        a = BitVecConstant(size=32, value=100)
        b = BitVecConstant(size=32, value=101)
        x = a + b
        self.assertTrue(isinstance(x, BitVec))

    def test_Expression_BoolTaint(self):
        # Bool can not be instantiaated
        self.assertRaises(Exception, Bool, ())

        x = BoolConstant(value=True, taint=("red",))
        y = BoolConstant(value=False, taint=("blue",))
        z = BoolOr(x, y)
        self.assertIn("red", x.taint)
        self.assertIn("blue", y.taint)
        self.assertIn("red", z.taint)
        self.assertIn("blue", z.taint)

    def test_Expression_BitVecTaint(self):
        # Bool can not be instantiaated
        self.assertRaises(Exception, BitVec, ())

        x = BitVecConstant(size=32, value=123, taint=("red",))
        y = BitVecConstant(size=32, value=124, taint=("blue",))
        z = BoolGreaterOrEqualThan(x, y)
        self.assertIn("red", x.taint)
        self.assertIn("blue", y.taint)
        self.assertIn("red", z.taint)
        self.assertIn("blue", z.taint)

    def test_Expression_Array(self):
        # Bool can not be instantiaated
        self.assertRaises(Exception, Array, ())

        a = ArrayConstant(index_size=32, value_size=8, value=b"ABCDE")
        a[0] == ord("A")

        x = BitVecConstant(size=32, value=123, taint=("red",))
        y = BitVecConstant(size=32, value=124, taint=("blue",))
        z = BoolGreaterOrEqualThan(x, y)
        self.assertIn("red", x.taint)
        self.assertIn("blue", y.taint)
        self.assertIn("red", z.taint)
        self.assertIn("blue", z.taint)


class ExpressionTestLoco(unittest.TestCase):
    _multiprocess_can_split_ = True

    def setUp(self):
        self.solver = Z3Solver.instance()
        cs = ConstraintSet()
        self.assertTrue(self.solver.check(cs))

    def assertItemsEqual(self, a, b):
        # Required for Python3 compatibility
        self.assertEqual(sorted(a), sorted(b))

    def tearDown(self):
        del self.solver

    def test_signed_unsigned_LT_(self):
        mask = (1 << 32) - 1

        cs = ConstraintSet()
        a = cs.new_bitvec(32)
        b = cs.new_bitvec(32)

        cs.add(a == 0x1)
        cs.add(b == (0x80000000 - 1))

        lt = b < a
        ult = b.ult(a)

        self.assertFalse(self.solver.can_be_true(cs, ult))
        self.assertTrue(self.solver.must_be_true(cs, Operators.NOT(lt)))

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


class ExpressionTest(unittest.TestCase):
    _multiprocess_can_split_ = False

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
        x = BitVecConstant(32, 10)
        cs = ConstraintSet()
        self.assertFalse(self.solver.can_be_true(cs, x == False))

    def test_constant_bitvec(self):
        """
        Tests if higher bits are masked out
        """
        x = BitVecConstant(32, 0xFF00000000)
        self.assertTrue(x.value == 0)

    def testBasicAST_001(self):
        """ Can't build abstract classes """
        a = BitVecConstant(32, 100)

        self.assertRaises(Exception, Expression, ())
        self.assertRaises(Exception, Constant, 123)
        self.assertRaises(Exception, Variable, "NAME")
        self.assertRaises(Exception, Operation, a)

    def testBasicOperation(self):
        """ Add """
        a = BitVecConstant(size=32, value=100)
        b = BitVecVariable(size=32, name="VAR")
        c = a + b
        self.assertIsInstance(c, BitVecAdd)
        self.assertIsInstance(c, Operation)
        self.assertIsInstance(c, Expression)

    def testBasicTaint(self):
        a = BitVecConstant(32, 100, taint=("SOURCE1",))
        b = BitVecConstant(32, 200, taint=("SOURCE2",))
        c = a + b
        self.assertIsInstance(c, BitVecAdd)
        self.assertIsInstance(c, Operation)
        self.assertIsInstance(c, Expression)
        self.assertTrue("SOURCE1" in c.taint)
        self.assertTrue("SOURCE2" in c.taint)

    def testBasicITETaint(self):
        a = BitVecConstant(32, 100, taint=("SOURCE1",))
        b = BitVecConstant(32, 200, taint=("SOURCE2",))
        c = BitVecConstant(32, 300, taint=("SOURCE3",))
        d = BitVecConstant(32, 400, taint=("SOURCE4",))
        x = Operators.ITEBV(32, a > b, c, d)
        self.assertTrue("SOURCE1" in x.taint)
        self.assertTrue("SOURCE2" in x.taint)
        self.assertTrue("SOURCE3" in x.taint)
        self.assertTrue("SOURCE4" in x.taint)

    def test_cs_new_bitvec_invalid_size(self):
        cs = ConstraintSet()
        with self.assertRaises(ValueError) as e:
            cs.new_bitvec(size=0)

        self.assertEqual(str(e.exception), "BitVec size (0) can't be equal to or less than 0")

        with self.assertRaises(ValueError) as e:
            cs.new_bitvec(size=-23)

        self.assertEqual(str(e.exception), "BitVec size (-23) can't be equal to or less than 0")

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
        bf = BoolConstant(False)
        bt = BoolConstant(True)
        cs.add(Operators.AND(bf, bt))
        self.assertFalse(self.solver.check(cs))

    def testBool2(self):
        cs = ConstraintSet()
        bf = BoolConstant(False)
        bt = BoolConstant(True)
        cs.add(Operators.AND(bf, bt, bt, bt))
        self.assertFalse(self.solver.check(cs))

    def testBool3(self):
        cs = ConstraintSet()
        bf = BoolConstant(False)
        bt = BoolConstant(True)
        cs.add(Operators.AND(bt, bt, bf, bt))
        self.assertFalse(self.solver.check(cs))

    def testBool4(self):
        cs = ConstraintSet()
        bf = BoolConstant(False)
        bt = BoolConstant(True)
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

    def testBasicArraySelectCache(self):
        cs = ConstraintSet()
        # make array of 32->8 bits
        array = cs.new_array(32, value_size=256)
        # make free 32bit bitvector
        key = cs.new_bitvec(32)

        expr1 = array[key]
        expr2 = array[key]
        self.assertTrue(hash(expr1) == hash(expr2))
        self.assertTrue(expr1 is expr2)
        self.assertTrue(simplify(expr1) is simplify(expr2))
        d = {}
        d[expr1] = 1
        d[expr2] = 2
        self.assertEqual(d[expr2], 2)

        """
        expr3 = expr1 + expr2
        expr4 = expr1 + expr2
        self.assertTrue(hash(expr3) == hash(expr4))

        b1 = expr3 == expr4
        b2 = expr3 == expr4
        d = {}
        d[expr3] = 3
        d[expr4] = 4

        key1 = cs.new_bitvec(32)
        key2 = cs.new_bitvec(32)

        expr1 = array[key1]
        expr2 = array[key2]
        self.assertTrue(expr1 is not expr2)
        self.assertTrue(simplify(expr1) is not simplify(expr2))


        expr1 = array[1]
        expr2 = array[1]
        self.assertTrue(expr1 is expr2)
        self.assertTrue(hash(expr1) == hash(expr2))
        self.assertTrue(simplify(expr1) is simplify(expr2))

        expr1 = array[1]
        expr2 = array[2]
        self.assertTrue(expr1 is not expr2)
        self.assertTrue(hash(expr1) != hash(expr2))
        self.assertTrue(simplify(expr1) is not simplify(expr2))

        expr1 = cs.new_bitvec(size=256)
        expr2 = cs.new_bitvec(size=32)
        self.assertFalse(hash(expr1) == hash(expr2))

        expr1 = cs.new_bitvec(size=256)
        expr2 = copy.copy(expr1)
        self.assertTrue(hash(expr1) == hash(expr2))

        expr1 = BitVecConstant(size=32, value=10)
        expr2 = BitVecConstant(size=32, value=10)
        self.assertTrue(hash(expr1) == hash(expr2))

        expr1 = BitVecConstant(size=32, value=10)
        expr2 = BitVecConstant(size=256, value=10)
        self.assertTrue(hash(expr1) != hash(expr2))
        """

    def testBasicArray256(self):
        cs = ConstraintSet()
        # make array of 32->8 bits
        array = cs.new_array(32, value_size=256)
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
        array = MutableArray(cs.new_array(index_size=32, value_size=32, name="array", default=0))
        key = cs.new_bitvec(32, name="key")
        index = cs.new_bitvec(32, name="index")

        array[key] = 1  # Write 1 to a single location

        cs.add(array.select(index) != 0)  # Constrain index so it selects that location

        cs.add(index != key)
        # key and index are the same there is only one slot in 1
        self.assertFalse(self.solver.check(cs))

    def testBasicArraySymbIdx2(self):
        cs = ConstraintSet()
        array = MutableArray(cs.new_array(index_size=32, value_size=32, name="array", default=0))
        key = cs.new_bitvec(32, name="key")
        index = cs.new_bitvec(32, name="index")

        array[key] = 1  # Write 1 to a single location
        cs.add(array.select(index) != 0)  # Constrain index so it selects that location
        a_index = self.solver.get_value(cs, index)  # get a concrete solution for index
        cs.add(array.select(a_index) != 0)  # now storage must have something at that location
        cs.add(a_index != index)  # remove it from the solutions

        # It should not be another solution for index
        self.assertFalse(self.solver.check(cs))

    def testBasicArrayDefault(self):
        cs = ConstraintSet()
        array = cs.new_array(index_size=32, value_size=32, name="array", default=0)
        key = cs.new_bitvec(32, name="key")
        self.assertTrue(self.solver.must_be_true(cs, array[key] == 0))

    def testBasicArrayDefault2(self):
        cs = ConstraintSet()
        array = MutableArray(cs.new_array(index_size=32, value_size=32, name="array", default=0))
        index1 = cs.new_bitvec(32)
        index2 = cs.new_bitvec(32)
        value = cs.new_bitvec(32)
        array[index2] = value
        cs.add(index1 != index2)
        cs.add(value != 0)
        self.assertTrue(self.solver.must_be_true(cs, array[index1] == 0))

    def testBasicArrayIndexConcrete(self):
        cs = ConstraintSet()
        array = MutableArray(cs.new_array(index_size=32, value_size=32, name="array", default=0))
        array[0] = 100
        self.assertTrue(array[0] == 100)

    def testBasicArrayConcatSlice(self):
        hw = b"Hello world!"
        cs = ConstraintSet()
        # make array of 32->8 bits
        array = cs.new_array(32, length=len(hw))
        array = array.write(0, hw)
        self.assertEqual(len(array), len(hw))
        self.assertTrue(self.solver.must_be_true(cs, array == hw))
        self.assertEqual(len(array.read(0, 12)), 12)
        x = array.read(0, 12) == hw

        self.assertTrue(self.solver.must_be_true(cs, array.read(0, 12) == hw))
        cs.add(array.read(6, 6) == hw[6:12])
        self.assertTrue(self.solver.must_be_true(cs, array.read(6, 6) == hw[6:12]))
        self.assertTrue(self.solver.must_be_true(cs, b"Hello " + array.read(6, 6) == hw))

        self.assertTrue(self.solver.must_be_true(cs, b"Hello " + array.read(6, 5) + b"!" == hw))

        self.assertTrue(
            self.solver.must_be_true(
                cs, array.read(0, 1) + b"ello " + array.read(6, 5) + b"!" == hw
            )
        )

        self.assertTrue(len(array[1:2]) == 1)

        self.assertTrue(len(array[0:12]) == 12)

        self.assertEqual(len(array[6:11]), 5)

        results = []
        for c in array[6:11]:
            results.append(c)
        self.assertEqual(len(results), 5)

    def testBasicArraySlice(self):
        hw = b"Hello world!"
        cs = ConstraintSet()
        # make array of 32->8 bits
        array = MutableArray(cs.new_array(32, length=12))
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
        array = MutableArray(cs.new_array(index_size=32, value_size=32, name="array", default=0))
        key = cs.new_bitvec(32, name="key")
        index = cs.new_bitvec(32, name="index")

        array[key] = 1  # Write 1 to a single location
        cs.add(array.select(index) != 0)  # Constrain index so it selects that location
        a_index = self.solver.get_value(cs, index)  # get a concrete solution for index

        cs.add(array.select(a_index) != 0)  # now storage must have something at that location
        cs.add(a_index != index)  # remove it from the solutions
        # It should not be another solution for index
        self.assertFalse(self.solver.check(cs))

    def testBasicArrayProxySymbIdx2(self):
        cs = ConstraintSet()
        array = MutableArray(cs.new_array(index_size=32, value_size=32, name="array", default=100))
        key = cs.new_bitvec(32, name="key")
        index = cs.new_bitvec(32, name="index")

        array[0] = 1  # Write 1 to first location
        array[key] = 2  # Write 2 to a symbolic (potentially any (potentially 0))location

        solutions = self.solver.get_all_values(cs, array[0])  # get a concrete solution for index
        self.assertItemsEqual(solutions, (1, 2))
        solutions = self.solver.get_all_values(
            cs, array.select(0)
        )  # get a concrete solution for index 0
        self.assertItemsEqual(solutions, (1, 2))

        solutions = self.solver.get_all_values(
            cs, array.select(1)
        )  # get a concrete solution for index 1 (default 100)
        self.assertItemsEqual(solutions, (100, 2))

    def testBasicConstatArray(self):
        cs = ConstraintSet()
        array1 = MutableArray(
            cs.new_array(index_size=32, value_size=32, length=10, name="array1", default=0)
        )
        array2 = MutableArray(
            cs.new_array(index_size=32, value_size=32, length=10, name="array2", default=0)
        )
        array1[0:10] = range(10)
        self.assertTrue(array1[0] == 0)
        # yeah right self.assertTrue(array1[0:10] == range(10))
        array_slice = array1[0:10]
        self.assertTrue(array_slice[0] == 0)

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

    def testBitVector_add(self):
        cs = ConstraintSet()
        a = cs.new_bitvec(32)
        b = cs.new_bitvec(32)
        c = cs.new_bitvec(32)
        cs.add(c == a + b)
        cs.add(a == 1)
        cs.add(b == 10)
        self.assertTrue(self.solver.check(cs))
        self.assertEqual(self.solver.get_value(cs, c), 11)

    def testBitVector_add1(self):
        cs = ConstraintSet()
        a = cs.new_bitvec(32)
        b = cs.new_bitvec(32)
        c = cs.new_bitvec(32)
        cs.add(c == a + 10)
        cs.add(a == 1)
        self.assertEqual(self.solver.check(cs), True)
        self.assertEqual(self.solver.get_value(cs, c), 11)

    def testBitVector_add2(self):
        cs = ConstraintSet()
        a = cs.new_bitvec(32)
        b = cs.new_bitvec(32)
        c = cs.new_bitvec(32)
        cs.add(11 == a + 10)
        self.assertTrue(self.solver.check(cs))
        self.assertEqual(self.solver.get_value(cs, a), 1)

    def testBitVector_max(self):
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

    def testBitVector_max_noop(self):
        from manticore import config

        consts = config.get_group("smt")
        consts.optimize = False
        self.testBitVector_max()
        consts.optimize = True

    def testBitVector_max1(self):
        cs = ConstraintSet()
        a = cs.new_bitvec(32)
        cs.add(a < 200)
        cs.add(a > 100)
        self.assertTrue(self.solver.check(cs))
        self.assertEqual(self.solver.minmax(cs, a), (101, 199))

    def testBitVector_max1_noop(self):
        from manticore import config

        consts = config.get_group("smt")
        consts.optimize = False
        self.testBitVector_max1()
        consts.optimize = True

    def testBool_nonzero(self):
        self.assertTrue(BoolConstant(True).__bool__())
        self.assertFalse(BoolConstant(False).__bool__())

    def test_visitors(self):
        solver = Z3Solver.instance()
        cs = ConstraintSet()
        arr = MutableArray(cs.new_array(name="MEM"))
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
        self.maxDiff = 5500
        print(translate_to_smtlib(aux))
        self.assertEqual(
            translate_to_smtlib(aux, use_bindings=False),
            "(select (store (store (store MEM #x00000000 #x61) #x00000001 #x62) #x00000003 (select (store (store MEM #x00000000 #x61) #x00000001 #x62) (bvadd VAR #x00000001))) (bvadd VAR ((_ zero_extend 24) (select (store (store (store MEM #x00000000 #x61) #x00000001 #x62) #x00000003 (select (store (store MEM #x00000000 #x61) #x00000001 #x62) (bvadd VAR #x00000001))) VAR))))",
        )

        self.assertEqual(
            translate_to_smtlib(aux, use_bindings=True),
            "(let ((!a_2! (store (store MEM #x00000000 #x61) #x00000001 #x62)) (!a_4! (store !a_2! #x00000003 (select !a_2! (bvadd VAR #x00000001)))) ) (select !a_4! (bvadd VAR ((_ zero_extend 24) (select !a_4! VAR)))))",
        )

        values = arr[0:2]
        self.assertEqual(len(values), 2)
        self.assertItemsEqual(solver.get_all_values(cs, values[0]), [ord("a")])
        self.assertItemsEqual(solver.get_all_values(cs, values[1]), [ord("b")])
        arr[1:3] = b"cd"

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

        x = BitVecConstant(32, 100, taint=("important",))
        y = BitVecConstant(32, 200, taint=("stuff",))
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
            translate_to_smtlib(exp), "(bvor (bvand (bvor BV #x00000000) #x00000001) #x00000000)"
        )
        exp = arithmetic_simplify(exp)
        self.assertTrue(get_depth(exp) < 4)
        self.assertEqual(translate_to_smtlib(exp), "(bvand BV #x00000001)")

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

    def test_arithmetic_simplify_udiv(self):
        cs = ConstraintSet()
        a = cs.new_bitvec(32, name="VARA")
        b = a + Operators.UDIV(BitVecConstant(32, 0), BitVecConstant(32, 2))
        self.assertEqual(translate_to_smtlib(b), "(bvadd VARA (bvudiv #x00000000 #x00000002))")
        self.assertEqual(translate_to_smtlib(simplify(b)), "VARA")

        c = a + Operators.UDIV(BitVecConstant(32, 2), BitVecConstant(32, 2))
        self.assertEqual(translate_to_smtlib(c), "(bvadd VARA (bvudiv #x00000002 #x00000002))")
        self.assertEqual(translate_to_smtlib(simplify(c)), "(bvadd VARA #x00000001)")

    def test_constant_folding_udiv(self):
        cs = ConstraintSet()
        x = BitVecConstant(32, 0xFFFFFFFF, taint=("important",))
        y = BitVecConstant(32, 2, taint=("stuff",))
        z = constant_folder(x.udiv(y))
        self.assertItemsEqual(z.taint, ("important", "stuff"))
        self.assertEqual(z.value, 0x7FFFFFFF)

    def test_simplify_OR(self):
        cs = ConstraintSet()
        bf = BoolConstant(False)
        bt = BoolConstant(True)
        var = cs.new_bool()
        cs.add(simplify(Operators.OR(var, var)) == var)
        cs.add(simplify(Operators.OR(var, bt)) == bt)
        self.assertTrue(self.solver.check(cs))

    def testBasicReplace(self):
        """ Add """
        a = BitVecConstant(size=32, value=100)
        b1 = BitVecVariable(size=32, name="VAR1")
        b2 = BitVecVariable(size=32, name="VAR2")

        c = a + b1

        x = replace(c, {b1: b2})
        self.assertEqual(translate_to_smtlib(x), "(bvadd #x00000064 VAR2)")

    def testBasicMigration(self):
        solver = Z3Solver.instance()
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
        solver = Z3Solver.instance()
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
        solver = Z3Solver.instance()
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
        solver = Z3Solver.instance()
        cs = ConstraintSet()
        a = cs.new_bitvec(8)
        cs.add(Operators.ORD(a) == Operators.ORD("Z"))

        self.assertTrue(solver.check(cs))
        self.assertEqual(solver.get_value(cs, a), ord("Z"))

    def test_ORD_proper_extract(self):
        solver = Z3Solver.instance()
        cs = ConstraintSet()
        a = cs.new_bitvec(32)
        cs.add(Operators.ORD(a) == Operators.ORD("\xff"))

        self.assertTrue(solver.check(cs))
        self.assertEqual(solver.get_value(cs, a), ord("\xff"))

    def test_CHR(self):
        solver = Z3Solver.instance()
        cs = ConstraintSet()
        self.assertTrue(solver.check(cs))
        a = cs.new_bitvec(8)
        cs.add(Operators.CHR(a) == Operators.CHR(0x41))

        self.assertTrue(solver.check(cs))
        self.assertEqual(solver.get_value(cs, a), 0x41)

    def test_CONCAT(self):
        solver = Z3Solver.instance()
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
        solver = Z3Solver.instance()
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
        solver = Z3Solver.instance()
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
        solver = Z3Solver.instance()
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
        solver = Z3Solver.instance()
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
        solver = Z3Solver.instance()
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
        solver = Z3Solver.instance()
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

        solver = Z3Solver.instance()
        cs1 = ConstraintSet()

        a1 = cs1.new_bitvec(8)
        b1 = cs1.new_bitvec(8)
        c1 = cs1.new_bitvec(8)
        d1 = cs1.new_bitvec(8)
        self.assertTrue(solver.check(cs1))

        cs1.add(b1 == 0x86)  # -122
        cs1.add(c1 == 0x11)  # 17
        cs1.add(a1 == Operators.SREM(b1, c1))
        cs1.add(d1 == b1.srem(c1))
        cs1.add(a1 == d1)

        self.assertTrue(solver.check(cs1))
        self.assertEqual(solver.get_value(cs1, a1), -3 & 0xFF)

    def test_SDIV(self):
        solver = Z3Solver.instance()
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
        solver = Z3Solver.instance()
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
        solver = Z3Solver.instance()
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
        solver = Z3Solver.instance()
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

    @unittest.skip("FIXME")
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


if __name__ == "__main__":
    unittest.main()
