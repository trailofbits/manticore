from manticore.core.smtlib import *
import unittest
import fcntl
import resource
import gc
import sys
#logging.basicConfig(filename = "test.log",
#                format = "%(asctime)s: %(name)s:%(levelname)s: %(message)s",
#                level = logging.DEBUG)

class ExpressionTest(unittest.TestCase):

    def setUp(self):
        self.solver = Z3Solver()
        

    def tearDown(self):
        del self.solver
        

    def testBasicAST_001(self):
        ''' Can't build abstract classes '''
        a = BitVecConstant(32, 100)

        self.assertRaises(TypeError, Expression, ())
        self.assertRaises(TypeError, Constant, 123)
        self.assertRaises(TypeError, Variable, 'NAME')
        self.assertRaises(TypeError, Operation, a)

    def testBasicOperation(self):
        ''' Add '''
        a = BitVecConstant(32, 100)
        b = BitVecVariable(32, 'VAR')
        c = a + b
        self.assertIsInstance(c, BitVecAdd)
        self.assertIsInstance(c, Operation)
        self.assertIsInstance(c, Expression)

    def testBasicTaint(self):
        a = BitVecConstant(32, 100, taint=('SOURCE1',))
        b = BitVecConstant(32, 200, taint=('SOURCE2',))
        c = a + b
        self.assertIsInstance(c, BitVecAdd)
        self.assertIsInstance(c, Operation)
        self.assertIsInstance(c, Expression)
        self.assertTrue('SOURCE1' in c.taint)
        self.assertTrue('SOURCE2' in c.taint)
    

    def testBasicConstraints(self):
        cs =  ConstraintSet()
        a = cs.new_bitvec(32)
        b = cs.new_bitvec(32)
        cs.add(a + b > 100)

    def testSolver(self):
        cs =  ConstraintSet()
        a = cs.new_bitvec(32)
        b = cs.new_bitvec(32)
        cs.add(a + b > 100)
        self.assertTrue(self.solver.check(cs))


    def testBool(self):
        cs =  ConstraintSet()
        bf = BoolConstant(False)
        bt = BoolConstant(True)
        cs.add( Operators.AND(bf, bt) )
        self.assertFalse(self.solver.check(cs))

    def testBasicArray(self):
        cs =  ConstraintSet()
        #make array of 32->8 bits
        array = cs.new_array(32)
        #make free 32bit bitvector 
        key = cs.new_bitvec(32)

        #assert that the array is 'A' at key position
        cs.add(array[key] == 'A')
        #lets restrict key to be greater than 1000
        cs.add(key.ugt(1000))

        with cs as temp_cs:
            #1001 position of array can be 'A'
            temp_cs.add(array[1001] == 'A')
            self.assertTrue(self.solver.check(temp_cs))
        
        with cs as temp_cs:
            #1001 position of array can also be 'B'
            temp_cs.add(array[1001] == 'B')
            self.assertTrue(self.solver.check(temp_cs))

        
        with cs as temp_cs:
            #but if it is 'B' ...
            temp_cs.add(array[1001] == 'B')
            #then key can not be 1001
            temp_cs.add(key == 1001)
            self.assertFalse(self.solver.check(temp_cs))

        with cs as temp_cs:
            #If 1001 position is 'B' ...
            temp_cs.add(array[1001] == 'B')
            #then key can be 1000 for ex..
            temp_cs.add(key == 1002)
            self.assertTrue(self.solver.check(temp_cs))

    def testBasicArrayStore(self):
        name = "bitarray"
        cs =  ConstraintSet()
        #make array of 32->8 bits
        array = cs.new_array(32, name=name)
        #make free 32bit bitvector 
        key = cs.new_bitvec(32)

        #assert that the array is 'A' at key position
        array = array.store(key, 'A')
        #lets restrict key to be greater than 1000
        cs.add(key.ugt(1000))

        #1001 position of array can be 'A'
        self.assertTrue(self.solver.can_be_true(cs, array.select(1001) == 'A'))

        #1001 position of array can be 'B'
        self.assertTrue(self.solver.can_be_true(cs, array.select(1001) == 'B'))

        #name is correctly proxied
        self.assertEqual(array.name, name + "_1")

        with cs as temp_cs:
            #but if it is 'B' ...
            temp_cs.add(array.select(1001) == 'B')
            #then key can not be 1001
            temp_cs.add(key == 1001)
            self.assertFalse(self.solver.check(temp_cs))

        with cs as temp_cs:
            #If 1001 position is 'B' ...
            temp_cs.add(array.select(1001) == 'B')
            #then key can be 1000 for ex..
            temp_cs.add(key != 1002)
            self.assertTrue(self.solver.check(temp_cs))

    def testBasicPickle(self):
        import pickle
        cs =  ConstraintSet()

        #make array of 32->8 bits
        array = cs.new_array(32)
        #make free 32bit bitvector 
        key = cs.new_bitvec(32)

        #assert that the array is 'A' at key position
        array = array.store(key, 'A')
        #lets restrict key to be greater than 1000
        cs.add(key.ugt(1000))
        cs = pickle.loads(pickle.dumps(cs))
        self.assertTrue(self.solver.check(cs))

    def testBitvector_add(self):
        cs =  ConstraintSet()
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
        cs.add(c == a+10)
        cs.add(a == 1)
        self.assertEqual(self.solver.check(cs), True)
        self.assertEqual(self.solver.get_value(cs, c), 11)

    def testBitvector_add2(self):
        cs = ConstraintSet()
        a = cs.new_bitvec(32)
        b = cs.new_bitvec(32)
        c = cs.new_bitvec(32)
        cs.add(11==a+10)
        self.assertTrue(self.solver.check(cs))
        self.assertEqual(self.solver.get_value(cs, a), 1)

    def testBitvector_max(self):
        cs = ConstraintSet()
        a = cs.new_bitvec(32)
        cs.add(a <= 200)
        cs.add(a >= 100)
        self.assertTrue(self.solver.check(cs))
        self.assertEqual(self.solver.minmax(cs, a), (100,200))

    def testBitvector_max1(self):
        cs = ConstraintSet()
        a = cs.new_bitvec(32)
        cs.add(a < 200)
        cs.add(a > 100)
        self.assertTrue(self.solver.check(cs))
        self.assertEqual(self.solver.minmax(cs, a), (101,199))

    def testBool_nonzero(self):
        self.assertTrue(BoolConstant(True).__nonzero__())
        self.assertFalse(BoolConstant(False).__nonzero__())

    def test_visitors(self):
        cs = ConstraintSet()
        arr = cs.new_array(name='MEM')
        a = cs.new_bitvec(32, name='VAR')
        self.assertEqual(get_depth(a), 1)
        cond = Operators.AND(a < 200, a > 100)
        arr[0]='a'
        arr[1]='b'



        self.assertEqual(get_depth(cond), 3)
        self.assertEqual(get_depth(arr[a+1]), 4)
        self.assertEqual(translate_to_smtlib(arr[a+1]), '(select (store (store MEM_1 #x00000000 #x61) #x00000001 #x62) (bvadd VAR_2 #x00000001))' )

        arr[3] = arr[a+1]
        aux = arr[a+Operators.ZEXTEND(arr[a],32)]

        self.assertEqual(get_depth(aux), 9)
        self.assertEqual(translate_to_smtlib(aux) ,'(select (store (store (store MEM_1 #x00000000 #x61) #x00000001 #x62) #x00000003 (select (store (store MEM_1 #x00000000 #x61) #x00000001 #x62) (bvadd VAR_2 #x00000001))) (bvadd VAR_2 ((_ zero_extend 24) (select (store (store (store MEM_1 #x00000000 #x61) #x00000001 #x62) #x00000003 (select (store (store MEM_1 #x00000000 #x61) #x00000001 #x62) (bvadd VAR_2 #x00000001))) VAR_2))))')

        values = arr[0:2]
        self.assertEqual(len(values), 2)
        self.assertItemsEqual(solver.get_all_values(cs, values[0]), [ord('a')])
        self.assertItemsEqual(solver.get_all_values(cs, values[1]), [ord('b')])
        arr[1:3] = 'cd'

        values = arr[0:3]
        self.assertEqual(len(values), 3)
        self.assertItemsEqual(solver.get_all_values(cs, values[0]), [ord('a')])
        self.assertItemsEqual(solver.get_all_values(cs, values[1]), [ord('c')])
        self.assertItemsEqual(solver.get_all_values(cs, values[2]), [ord('d')])
        self.assertEqual(pretty_print(aux, depth=2), 'ArraySelect\n  ArrayStore\n    ...\n  BitVecAdd\n    ...\n')

        x = BitVecConstant(32, 100, taint=('important',))
        y = BitVecConstant(32, 200, taint=('stuff',))
        z = constant_folder(x+y)
        self.assertItemsEqual(z.taint, ('important', 'stuff')) 
        self.assertEqual(z.value, 300) 

    def test_arithmetic_simplifier(self):
        cs = ConstraintSet()
        arr = cs.new_array(name='MEM')
        a = cs.new_bitvec(32, name='VARA')
        b = cs.new_bitvec(32, name='VARB')
        c = a*2+b
        self.assertEqual( translate_to_smtlib(c), '(bvadd (bvmul VARA_2 #x00000002) VARB_3)')
        self.assertEqual( translate_to_smtlib((c+4)-4), '(bvsub (bvadd (bvadd (bvmul VARA_2 #x00000002) VARB_3) #x00000004) #x00000004)')

        d = c+4
        s = arithmetic_simplifier(d-c)
        self.assertIsInstance(s, Constant)
        self.assertEqual(s.value, 4)
        #size = arithmetic_simplifier(size

        cs2 = ConstraintSet()
        exp = cs2.new_bitvec(32)
        exp |=  0
        exp &= 1	
        exp |= 0
        self.assertEqual(get_depth(exp), 4)
        self.assertEqual(translate_to_smtlib(exp), '(bvor (bvand (bvor V_1 #x00000000) #x00000001) #x00000000)')
        exp = arithmetic_simplifier(exp)
        self.assertTrue(get_depth(exp) < 4)
        self.assertEqual(translate_to_smtlib(exp), '(bvand V_1 #x00000001)')

    def test_ORD(self):
        cs = ConstraintSet()
        a = cs.new_bitvec(8)
        cs.add(Operators.ORD(a) == Operators.ORD('Z'))

        self.assertTrue(solver.check(cs))
        self.assertEqual(solver.get_value(cs, a), ord('Z'))

    def test_CHR(self):
        cs = ConstraintSet()
        a = cs.new_bitvec(8)
        cs.add(Operators.CHR(a) == Operators.CHR(0x41))

        self.assertTrue(solver.check(cs))
        self.assertEqual(solver.get_value(cs, a), 0x41)

    def test_CONCAT(self):
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
        cs = ConstraintSet()
        a = cs.new_bitvec(8)
        b = cs.new_bitvec(8)
        c = cs.new_bitvec(8)

        cs.add(b == 0x41)
        cs.add(c == 0x42)
        cs.add(a == Operators.ITEBV(8, b==c, b, c))

        self.assertTrue(solver.check(cs))
        self.assertEqual(solver.get_value(cs, a), 0x42)

    def test_ITEBV_2(self):
        cs = ConstraintSet()
        a = cs.new_bitvec(8)
        b = cs.new_bitvec(8)
        c = cs.new_bitvec(8)

        cs.add(b == 0x44)
        cs.add(c == 0x44)
        cs.add(a == Operators.ITEBV(8, b==c, b, c))

        self.assertTrue(solver.check(cs))
        self.assertEqual(solver.get_value(cs, a), 0x44)

    def test_ITE(self):
        cs = ConstraintSet()
        a = cs.new_bool()
        b = cs.new_bool()
        c = cs.new_bool()

        cs.add(b == True)
        cs.add(c == False)
        cs.add(a == Operators.ITE(b==c, b, c))

        self.assertTrue(solver.check(cs))
        self.assertEqual(solver.get_value(cs, a), False)

    def test_UREM(self):
        cs = ConstraintSet()
        a = cs.new_bitvec(8)
        b = cs.new_bitvec(8)
        c = cs.new_bitvec(8)
        d = cs.new_bitvec(8)

        cs.add(b == 0x86) #134
        cs.add(c == 0x11) #17
        cs.add(a == Operators.UREM(b, c))
        cs.add(d == b.urem(c))
        cs.add(a == d)

        self.assertTrue(solver.check(cs))
        self.assertEqual(solver.get_value(cs, a), 0xF)

    def test_SREM(self):
        cs = ConstraintSet()
        a = cs.new_bitvec(8)
        b = cs.new_bitvec(8)
        c = cs.new_bitvec(8)
        d = cs.new_bitvec(8)

        cs.add(b == 0x86) #-122
        cs.add(c == 0x11) #17
        cs.add(a == Operators.SREM(b, c))
        cs.add(d == b.srem(c))
        cs.add(a == d)

        self.assertTrue(solver.check(cs))
        self.assertEqual(solver.get_value(cs, a), -3&0xFF)

    def test_UDIV(self):
        cs = ConstraintSet()
        a = cs.new_bitvec(8)
        b = cs.new_bitvec(8)
        c = cs.new_bitvec(8)
        d = cs.new_bitvec(8)

        cs.add(b == 0x86) #134
        cs.add(c == 0x11) #17
        cs.add(a == Operators.UDIV(b, c))
        cs.add(d == b.udiv(c))
        cs.add(a == d)

        self.assertTrue(solver.check(cs))
        self.assertEqual(solver.get_value(cs, a), 7)

    def test_SDIV(self):
        cs = ConstraintSet()
        a = cs.new_bitvec(8)
        b = cs.new_bitvec(8)
        c = cs.new_bitvec(8)
        d = cs.new_bitvec(8)

        cs.add(b == 0x86) #-122
        cs.add(c == 0x11) #17
        cs.add(a == Operators.SDIV(b, c))
        cs.add(d == b/c)
        cs.add(a == d)

        self.assertTrue(solver.check(cs))
        self.assertEqual(solver.get_value(cs, a), -7&0xFF)


    def test_SAR(self):
        A = 0xbadf00d
        for B in xrange(32):
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
        import pickle
        cs =  ConstraintSet()
        #make free 32bit bitvectors
        x = cs.new_bitvec(8)
        y = cs.new_bitvec(8)

        #linear relation
        #cs.add(x+y*5 == 0)

        #Fork and divide in quadrants 

        saved_up = None
        saved_up_right = None
        saved_up_left = None
        saved_down = None
        saved_down_right = None
        saved_down_left = None


        with cs as cs_up:
            cs_up.add(y.uge(0x80))
            self.assertItemsEqual(solver.get_all_values(cs_up, x), range(0x0, 0x100))
            self.assertItemsEqual(solver.get_all_values(cs_up, y), range(0x80,0x100))

            saved_up = pickle.dumps((x,y,cs_up))

            self.assertItemsEqual(solver.get_all_values(cs_up, x), range(0x0, 0x100))
            self.assertItemsEqual(solver.get_all_values(cs_up, y), range(0x80,0x100))

            with cs_up as cs_up_right:
                cs_up_right.add(x.uge(0x80))
                saved_up_right = pickle.dumps((x,y,cs_up_right))
                self.assertItemsEqual(solver.get_all_values(cs_up_right, x), range(0x80, 0x100))
                self.assertItemsEqual(solver.get_all_values(cs_up_right, y), range(0x80, 0x100))

            self.assertItemsEqual(solver.get_all_values(cs_up, x), range(0x0, 0x100))
            self.assertItemsEqual(solver.get_all_values(cs_up, y), range(0x80,0x100))

            with cs_up as cs_up_left:
                cs_up_left.add(x.ult(0x80))
                saved_up_left = pickle.dumps((x,y,cs_up_left))
                self.assertItemsEqual(solver.get_all_values(cs_up_left, x), range(0, 0x80))
                self.assertItemsEqual(solver.get_all_values(cs_up_left, y), range(0x80, 0x100))

            self.assertItemsEqual(solver.get_all_values(cs_up, x), range(0x0, 0x100))
            self.assertItemsEqual(solver.get_all_values(cs_up, y), range(0x80,0x100))


        with cs as cs_down:
            cs_down.add(y.ult(0x80))

            self.assertItemsEqual(solver.get_all_values(cs_down, x), range(0x0, 0x100))
            self.assertItemsEqual(solver.get_all_values(cs_down, y), range(0, 0x80))

            saved_down = pickle.dumps((x,y,cs_down))

            self.assertItemsEqual(solver.get_all_values(cs_down, x), range(0x0, 0x100))
            self.assertItemsEqual(solver.get_all_values(cs_down, y), range(0, 0x80))


            with cs_down as cs_down_right:
                cs_down_right.add(x.uge(0x80))
                saved_down_right = pickle.dumps((x,y,cs_down_right))
                self.assertItemsEqual(solver.get_all_values(cs_down_right, x), range(0x80, 0x100))
                self.assertItemsEqual(solver.get_all_values(cs_down_right, y), range(0, 0x80))

            self.assertItemsEqual(solver.get_all_values(cs_down, x), range(0x0, 0x100))
            self.assertItemsEqual(solver.get_all_values(cs_down, y), range(0, 0x80))

            with cs_down as cs_down_left:
                cs_down_left.add(x.ult(0x80))
                saved_down_left = pickle.dumps((x,y,cs_down_left))
                self.assertItemsEqual(solver.get_all_values(cs_down_left, x), range(0, 0x80))
                self.assertItemsEqual(solver.get_all_values(cs_down_left, y), range(0, 0x80))

            self.assertItemsEqual(solver.get_all_values(cs_down, x), range(0x0, 0x100))
            self.assertItemsEqual(solver.get_all_values(cs_down, y), range(0, 0x80))


            x,y,cs_up= pickle.loads(saved_up)
            self.assertItemsEqual(solver.get_all_values(cs_up, x), range(0x0, 0x100))
            self.assertItemsEqual(solver.get_all_values(cs_up, y), range(0x80, 0x100))

            x,y,cs_up_right= pickle.loads(saved_up_right)
            self.assertItemsEqual(solver.get_all_values(cs_up_right, x), range(0x80, 0x100))
            self.assertItemsEqual(solver.get_all_values(cs_up_right, y), range(0x80, 0x100))

            x,y,cs_up_left= pickle.loads(saved_up_left)
            self.assertItemsEqual(solver.get_all_values(cs_up_left, x), range(0x00, 0x80))
            self.assertItemsEqual(solver.get_all_values(cs_up_left, y), range(0x80, 0x100))

            x,y, cs_down= pickle.loads(saved_down)
            self.assertItemsEqual(solver.get_all_values(cs_down, x), range(0x0, 0x100))
            self.assertItemsEqual(solver.get_all_values(cs_down, y), range(0x0, 0x80))

            x,y,cs_down_right= pickle.loads(saved_down_right)
            self.assertItemsEqual(solver.get_all_values(cs_down_right, x), range(0x80, 0x100))
            self.assertItemsEqual(solver.get_all_values(cs_down_right, y), range(0x00, 0x80))

            x,y,cs_down_left= pickle.loads(saved_down_left)
            self.assertItemsEqual(solver.get_all_values(cs_down_left, x), range(0x00, 0x80))
            self.assertItemsEqual(solver.get_all_values(cs_down_left, y), range(0x00, 0x80))

    def test_ORD(self):
        cs = ConstraintSet()
        a = cs.new_bitvec(8)
        cs.add(Operators.ORD(a) == Operators.ORD('Z'))

        self.assertTrue(solver.check(cs))
        self.assertEqual(solver.get_value(cs, a), ord('Z'))

    def test_CHR(self):
        cs = ConstraintSet()
        a = cs.new_bitvec(8)
        cs.add(Operators.CHR(a) == Operators.CHR(0x41))

        self.assertTrue(solver.check(cs))
        self.assertEqual(solver.get_value(cs, a), 0x41)

    def test_CONCAT(self):
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
        cs = ConstraintSet()
        a = cs.new_bitvec(8)
        b = cs.new_bitvec(8)
        c = cs.new_bitvec(8)

        cs.add(b == 0x41)
        cs.add(c == 0x42)
        cs.add(a == Operators.ITEBV(8, b==c, b, c))

        self.assertTrue(solver.check(cs))
        self.assertEqual(solver.get_value(cs, a), 0x42)

    def test_ITEBV_2(self):
        cs = ConstraintSet()
        a = cs.new_bitvec(8)
        b = cs.new_bitvec(8)
        c = cs.new_bitvec(8)

        cs.add(b == 0x44)
        cs.add(c == 0x44)
        cs.add(a == Operators.ITEBV(8, b==c, b, c))

        self.assertTrue(solver.check(cs))
        self.assertEqual(solver.get_value(cs, a), 0x44)

    def test_ITE(self):
        cs = ConstraintSet()
        a = cs.new_bool()
        b = cs.new_bool()
        c = cs.new_bool()

        cs.add(b == True)
        cs.add(c == False)
        cs.add(a == Operators.ITE(b==c, b, c))

        self.assertTrue(solver.check(cs))
        self.assertEqual(solver.get_value(cs, a), False)

    def test_UREM(self):
        cs = ConstraintSet()
        a = cs.new_bitvec(8)
        b = cs.new_bitvec(8)
        c = cs.new_bitvec(8)
        d = cs.new_bitvec(8)

        cs.add(b == 0x86) #134
        cs.add(c == 0x11) #17
        cs.add(a == Operators.UREM(b, c))
        cs.add(d == b.urem(c))
        cs.add(a == d)

        self.assertTrue(solver.check(cs))
        self.assertEqual(solver.get_value(cs, a), 0xF)

    def test_SREM(self):
        cs = ConstraintSet()
        a = cs.new_bitvec(8)
        b = cs.new_bitvec(8)
        c = cs.new_bitvec(8)
        d = cs.new_bitvec(8)

        cs.add(b == 0x86) #-122
        cs.add(c == 0x11) #17
        cs.add(a == Operators.SREM(b, c))
        cs.add(d == b.srem(c))
        cs.add(a == d)

        self.assertTrue(solver.check(cs))
        self.assertEqual(solver.get_value(cs, a), -3&0xFF)

    def test_UDIV(self):
        cs = ConstraintSet()
        a = cs.new_bitvec(8)
        b = cs.new_bitvec(8)
        c = cs.new_bitvec(8)
        d = cs.new_bitvec(8)

        cs.add(b == 0x86) #134
        cs.add(c == 0x11) #17
        cs.add(a == Operators.UDIV(b, c))
        cs.add(d == b.udiv(c))
        cs.add(a == d)

        self.assertTrue(solver.check(cs))
        self.assertEqual(solver.get_value(cs, a), 7)

    def test_SDIV(self):
        cs = ConstraintSet()
        a = cs.new_bitvec(8)
        b = cs.new_bitvec(8)
        c = cs.new_bitvec(8)
        d = cs.new_bitvec(8)

        cs.add(b == 0x86) #-122
        cs.add(c == 0x11) #17
        cs.add(a == Operators.SDIV(b, c))
        cs.add(d == b/c)
        cs.add(a == d)

        self.assertTrue(solver.check(cs))
        self.assertEqual(solver.get_value(cs, a), -7&0xFF)

import importlib
class Z3Test(unittest.TestCase):
    def setUp(self):
        #Manual mock for check_output 
        self.module = importlib.import_module('manticore.core.smtlib.solver')
        self.module.check_output = lambda *args, **kwargs: self.version
        self.z3 = self.module.Z3Solver

    def test_check_solver_min(self):
        self.version = 'Z3 version 4.4.1'
        self.assertTrue(self.z3._solver_version() == Version(major=4, minor=4, patch=1))

    def test_check_solver_newer(self):
        self.version = 'Z3 version 4.5.0'
        self.assertTrue(self.z3._solver_version() > Version(major=4, minor=4, patch=1))

    def test_check_solver_optimize(self):
        self.version = 'Z3 version 4.5.0'
        solver = self.z3()
        self.assertTrue(solver.support_maximize)
        self.assertTrue(solver.support_minimize)

    def test_check_solver_optimize(self):
        self.version = 'Z3 version 4.4.0'
        solver = self.z3()
        self.assertFalse(solver.support_maximize)
        self.assertFalse(solver.support_minimize)

if __name__ == '__main__':
    unittest.main()


