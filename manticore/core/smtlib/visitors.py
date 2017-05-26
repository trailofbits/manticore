from abc import ABCMeta, abstractmethod, abstractproperty
from expression import *
import logging
logger = logging.getLogger("VISITOR")


class Visitor(object):
    __metaclass__ = ABCMeta
    ''' Class/Type Visitor

       Inherit your class visitor from this one and get called on a different
       visiting function for each type of expression. It will call the first
       implemented method for the __mro__ class order.
        For example for a BitVecAdd it will try
            visit_BitVecAdd()          if not defined then it will try with
            visit_BitVecOperation()    if not defined then it will try with
            visit_BitVec()             if not defined then it will try with
            visit_Operation()          if not defined then it will try with
            visit_Expression()

        Other class named visitors are:

        vistit_Constant()
        vistit_Variable()
        vistit_Operation()
        vistit_BitVec()
        vistit_Bool()
        vistit_Array()

    '''
    def __init__(self, **kwargs):
        super(Visitor, self).__init__()
        self._stack = []
        self._cache = {}

    def push(self, value):
        assert value is not None
        self._stack.append(value)

    def pop(self):
        if len(self._stack) == 0:
            return None
        result = self._stack.pop()
        assert result is not None
        return result

    @property
    def result(self):
        assert len(self._stack) == 1
        return self.pop()

    def _method(self, expression, *args):
        assert expression.__class__.__mro__[-1] is object 
        for cls in expression.__class__.__mro__:
            sort = cls.__name__
            methodname = 'visit_%s' % sort
            if hasattr(self, methodname):
                value = getattr(self, methodname)(expression, *args)
                if value is not None:
                    return value
        return expression

    def visit(self, node, use_fixed_point=False):
        '''
        The entry point of the visitor.
        The exploration algorithm is a DFS post-order traversal
        The implementation used two stacks instead of a recursion
        The final result is store in self.result

        :param node: Node to explore
        :type node: Expression
        :param use_fixed_point: if True, it runs _methods until a fixed point is found
        :type use_fixed_point: Bool
        '''   
        cache = self._cache

        visited = set()
        stack = []
        stack.append(node)
        while stack:
            node = stack.pop()
 
            if node in cache:
                self.push(cache[node])
            elif isinstance(node, Operation):
                if node in visited:
                    operands = [self.pop() for _ in xrange(len(node.operands))]
                    if use_fixed_point:
                        new_node = self._rebuild(node, operands)
                        value = self._method(new_node, *operands)
                        while value is not new_node:
                            new_node = value
                            if isinstance(new_node, Operation):
                                value = self._method(new_node, *new_node.operands)
                    else:
                        value = self._method(node, *operands)
                    visited.remove(node)
                    self.push(value)
                    cache[node] = value
                else:
                    visited.add(node)
                    stack.append(node)
                    stack.extend(node.operands)
            else:
                self.push(self._method(node))

    @staticmethod
    def _rebuild(expression, operands):
        if isinstance(expression, Operation):
            import copy
            aux = copy.copy(expression)
            aux._operands = operands
            return aux
        return type(expression)(*operands, taint=expression.taint)

class GetDeclarations(Visitor):
    ''' Simple visitor to collect all variables in an expression or set of
        expressions
    '''
    def __init__(self, **kwargs):
        super(GetDeclarations, self).__init__(**kwargs)
        self.variables = set()

    def visit_Variable(self, expression):
        self.variables.add(expression)
        return expression

    @property
    def result(self):
        return self.variables

def get_variables(expression):
    visitor = GetDeclarations()
    visitor.visit(expression)
    return visitor.result

class GetDepth(Visitor):
    ''' Simple visitor to collect all variables in an expression or set of
        expressions
    '''
    def __init__(self, *args, **kwargs):
        super(GetDepth, self).__init__(*args, **kwargs)

    def visit_Expression(self, expression):
        return 1

    def visit_Operation(self, expression, *operands):
        return 1 + max(operands) 

def get_depth(exp):
    visitor = GetDepth()
    visitor.visit(exp)
    return visitor.result

class PrettyPrinter(Visitor):
    def __init__(self, depth=None,  **kwargs):
        super(PrettyPrinter, self).__init__(**kwargs)
        self.output = ''
        self.indent = 0
        self.depth = depth

    def _print(self, s, e=None):
        self.output += ' '*self.indent + str(s) # + '(%016x)'%hash(e)
        self.output += '\n'

    def visit(self, expression):
        '''
        Overload Visitor.visit because:
        - We need a pre-order traversal
        - We use a recursion as it makes eaiser to keep track of the indentation

        '''
        self._method(expression)

    def _method(self, expression, *args):
        '''
        Overload Visitor._method because we want to stop to iterate over the
        visit_ functions as soon as a valide visit_ function is found
        '''
        assert expression.__class__.__mro__[-1] is object
        for cls in expression.__class__.__mro__:
            sort = cls.__name__
            methodname = 'visit_%s' % sort
            method = getattr(self, methodname, None)
            if method is not None:
                method(expression, *args)
                return
        return

    def visit_Operation(self, expression, *operands):
        self._print(expression.__class__.__name__, expression)
        self.indent += 2
        if self.depth is None or self.indent < self.depth*2:
            for o in expression.operands:
                self.visit(o)
        else:
            self._print('...')
        self.indent -= 2
        return ''

    def visit_BitVecExtract(self, expression):
        self._print(expression.__class__.__name__+'{%d:%d}'%(expression.begining,expression.end), expression)
        self.indent += 2
        if self.depth is None or self.indent < self.depth*2:
            for o in expression.operands:
                self.visit(o)
        else:
            self._print('...')
        self.indent -= 2
        return ''

    def visit_Constant(self, expression):
        self._print(expression.value)
        return ''

    def visit_Variable(self, expression):
        self._print(expression.name)
        return ''
       
    @property
    def result(self):
        return self.output


def pretty_print(expression, **kwargs):
    pp = PrettyPrinter(**kwargs)
    pp.visit(expression)
    return pp.result


class ConstantFolderSimplifier(Visitor):
    def __init__(self, **kw):
        super(ConstantFolderSimplifier, self).__init__(**kw)

    operations = {  BitVecAdd : operator.__add__ ,
                    BitVecSub : operator.__sub__ ,
                    BitVecMul : operator.__mul__ ,
                    BitVecDiv : operator.__div__ ,
                    BitVecShiftLeft : operator.__lshift__ ,
                    BitVecShiftRight : operator.__rshift__ ,
                    BitVecAnd : operator.__and__ ,
                    BitVecOr : operator.__or__ ,
                    BitVecXor : operator.__xor__ ,
                    BitVecNot : operator.__not__ ,
                    BitVecNeg : operator.__invert__ ,
                    LessThan : operator.__lt__ ,
                    LessOrEqual : operator.__le__ ,
                    Equal : operator.__eq__ ,
                    GreaterThan : operator.__gt__ ,
                    GreaterOrEqual : operator.__ge__ ,
                 }

    def visit_BitVecConcat(self, expression, *operands):
        if all( isinstance(o, Constant) for o in operands):
            result = 0
            for o in operands:
                result <<= o.size
                result |= o.value 
            return BitVecConstant(expression.size, result, taint=expression.taint)
        
    def visit_BitVecZeroExtend(self, expression, *operands):
        if all( isinstance(o, Constant) for o in operands):
            return BitVecConstant(expression.size, operands[0].value, taint=expression.taint)

    def visit_BitVecExtract(self, expression, *operands):
        if all( isinstance(o, Constant) for o in expression.operands):
            value=expression.operands[0].value
            begining = expression.begining
            end = expression.end
            value = value >> begining
            mask = 2**(end - begining +1) - 1
            value = value & mask
            return BitVecConstant(expression.size, value, taint=expression.taint)

    def visit_Operation(self, expression, *operands):
        ''' constant folding, if all operands of an expression are a Constant do the math '''
        operation = self.operations.get(type(expression), None)
        if operation is not None and \
                all( isinstance(o, Constant) for o in operands) :
            value = operation(*(x.value for x in operands))
            if isinstance(expression, BitVec):
                return BitVecConstant(expression.size, value, taint=expression.taint)
            else:
                isinstance(expression, Bool)
                return BoolConstant(value, taint=expression.taint)
        else:
            if any( operands[i] is not expression.operands[i] for i in xrange(len(operands))):
                expression = type(expression)(*operands, taint=expression.taint)
        return expression


def constant_folder(expression):
    simp = ConstantFolderSimplifier()
    simp.visit(expression)
    return simp.result

class ArithmeticSimplifier(Visitor):
    def __init__(self, parent=None, **kw):
        super(ArithmeticSimplifier, self).__init__(**kw)

    @staticmethod
    def _same_constant(a,b):
        return isinstance(a, Constant) and\
           isinstance(b, Constant) and\
            a.value == b.value or a is b

    @staticmethod
    def _changed(expression, operands):
        arity = len(operands)
        return any( operands[i] is not expression.operands[i] for i in range(arity))

    def visit_Operation(self, expression, *operands):
        ''' constant folding, if all operands of an expression are a Constant do the math '''
        if all( isinstance(o, Constant) for o in operands) :
            expression = constant_folder(expression)
        if self._changed(expression, operands):
            expression = self._rebuild(expression, operands)
        return expression

    def visit_BitVecZeroExtend(self, expression, *operands):
        if self._changed(expression, operands):
            return BitVecZeroExtend(expression.size, *operands, taint=expression.taint)
        else:
            return expression

    def visit_BitVecITE(self, expression, *operands):
        if isinstance( expression.operands[0], Constant):
            if expression.operands[0].value:
                return expression.operands[1]
            else:
                return expression.operands[2]
        if self._changed(expression, operands):
            return BitVecITE(expression.size, *operands, taint=expression.taint)

    def visit_BitVecExtract(self, expression, *operands):
        ''' extract(0,sizeof(a))(a)  ==> a
            extract(0, 16 )( concat(a,b,c,d) ) => concat(c, d)
        '''
        op = expression.operands[0]
        begining = expression.begining
        end = expression.end 

        if isinstance(op, BitVecConcat):
            new_operands = []
            bitcount = 0
            for item in reversed(op.operands):
                if begining >= item.size:
                    begining -= item.size
                else:
                    if bitcount < expression.size:
                        new_operands.append(item)
                    bitcount += item.size
            if begining != expression.begining:
                return BitVecExtract(BitVecConcat(sum(map(lambda x: x.size, new_operands)), *reversed(new_operands)), begining, expression.size, taint=expression.taint)
        
    def visit_BitVecAdd(self, expression, *operands):
        ''' a + 0  ==> a
            0 + a  ==> a 
        '''
        left = expression.operands[0]
        right = expression.operands[1]
        if isinstance(right, BitVecConstant):
            if right.value == 0:
                return left
        if isinstance(left, BitVecConstant):
            if left.value == 0:
                return right

    def visit_BitVecSub(self, expression, *operands):
        ''' a - 0 ==> 0
            (a + b) - b  ==> a 
            (b + a) - b  ==> a 
        '''
        left = expression.operands[0]
        right = expression.operands[1]
        if isinstance(left, BitVecAdd):
            if self._same_constant( left.operands[0], right):
                return left.operands[1]
            elif self._same_constant(left.operands[1], right):
                return left.operands[0]
        
    def visit_BitVecOr(self, expression, *operands):
        ''' a | 0 => a
            0 | a => a
            0xffffffff & a => 0xffffffff
            a & 0xffffffff => 0xffffffff

        '''
        left = expression.operands[0]
        right = expression.operands[1]
        if isinstance( right, BitVecConstant):
            if right.value == 0:
                return left
            elif right.value == left.mask:
                return right
            elif isinstance(left, BitVecOr):
                left_left = left.operands[0]
                left_right = left.operands[1]
                if isinstance(right, Constant):
                    return BitVecOr(left_left, (left_right|right), taint=expression.taint)
        elif isinstance(left, BitVecConstant):
            return BitVecOr(right, left, taint=expression.taint)


    def visit_BitVecAnd(self, expression, *operands):
        ''' ct & x => x & ct                move constants to the right
            a & 0 => 0                      remove zero
            a & 0xffffffff => a             remove full mask
            (b & ct2) & ct => b & (ct&ct2)  ?
            (a & (b | c) => a&b | a&c       distribute over |
        '''
        left = expression.operands[0]
        right = expression.operands[1]
        if isinstance(right, BitVecConstant):
            if right.value == 0:
                return right
            elif right.value == right.mask:
                return left
            elif isinstance(left, BitVecAnd):
                left_left = left.operands[0]
                left_right = left.operands[1]
                if isinstance(right, Constant):
                    return BitVecAnd(left_left, left_right&right, taint=expression.taint)
            elif isinstance(left, BitVecOr):
                left_left = left.operands[0]
                left_right = left.operands[1]
                return BitVecOr(right&left_left, right&left_right, taint=expression.taint)

        elif isinstance(left, BitVecConstant):
            return BitVecAnd(right, left, taint=expression.taint)
        

    def visit_BitVecShiftLeft(self, expression, *operands):
        ''' a << 0 => a                       remove zero
            a << ct => 0 if ct > sizeof(a)    remove big constant shift
        '''
        left = expression.operands[0]
        right = expression.operands[1]
        if isinstance(right, BitVecConstant):
            if right.value == 0:
                return left
            elif right.value >= right.size:
                return left

    def visit_ArraySelect(self, expression, *operands):
        ''' ArraySelect (ArrayStore((ArrayStore(x0,v0) ...),xn, vn), x0)
                -> v0
        '''
        arr = expression.array
        index = expression.index
        if isinstance(index, BitVecConstant):
            index = index.value
            prev_arr = arr
            while isinstance(arr, ArrayStore):
               prev_arr = arr
               index_store = arr.index
               if isinstance(index_store, BitVecConstant):
                   if index_store.value == index:
                       return arr.byte
                   arr = arr.array
               else:
                    break


    def visit_Expression(self, expression, *operands):
        assert len(operands) == 0
        assert not isinstance(expression, Operation)
        return expression
        
def arithmetic_simplifier(expression):
    simp = ArithmeticSimplifier()
    simp.visit(expression, use_fixed_point=True)
    return simp.result

class TranslatorSmtlib(Visitor):
    ''' Simple visitor to translate an expression to its smtlib representation
    '''
    unique = 0
    def __init__(self, use_bindings=False, *args, **kw):
        assert 'bindings' not in kw
        super(TranslatorSmtlib, self).__init__(*args, **kw)
        self.use_bindings=use_bindings
        self._bindings = []


    def _add_binding(self, expression, smtlib):
        if not self.use_bindings or len(smtlib) <= 10:
            return smtlib
        '''
        for nm, exp, smt in self._bindings:
            if expression is exp:
                return nm #fixme change to dict
            if smtlib == smt:
                return nm #fixme change to dict
        '''
        TranslatorSmtlib.unique+=1
        name ='aux%d'% TranslatorSmtlib.unique

        self._bindings.append((name, expression, smtlib))

        self._cache[expression] = name
        return name

    @property
    def bindings(self):
        return self._bindings

    translation_table = {
        BoolNot: 'not',
        BoolEq: '=',
        BoolAnd: 'and',
        BoolOr: 'or',
        BoolXor: 'xor',
        BoolITE: 'ite',
        BitVecAdd: 'bvadd',
        BitVecSub: 'bvsub',
        BitVecMul: 'bvmul',
        BitVecDiv: 'bvsdiv',
        BitVecUnsignedDiv: 'bvudiv',
        BitVecMod: 'bvsmod',
        BitVecRem: 'bvsrem',
        BitVecUnsignedRem: 'bvurem',
        BitVecShiftLeft: 'bvshl',
        BitVecShiftRight: 'bvlshr',
        BitVecArithmeticShiftLeft: 'bvashl',
        BitVecArithmeticShiftRight: 'bvashr',
        BitVecAnd: 'bvand',
        BitVecOr: 'bvor',
        BitVecXor: 'bvxor',
        BitVecNot: 'bvnot',
        BitVecNeg: 'bvneg',
        LessThan: 'bvslt',
        LessOrEqual: 'bvsle',
        Equal: '=',
        GreaterThan: 'bvsgt',
        GreaterOrEqual: 'bvsge',
        UnsignedLessThan: 'bvult',
        UnsignedLessOrEqual: 'bvule',
        UnsignedGreaterThan: 'bvugt',
        UnsignedGreaterOrEqual: 'bvuge',
        ArraySelect: 'select',
        BitVecSignExtend: '(_ sign_extend %d)',
        BitVecZeroExtend: '(_ zero_extend %d)',
        BitVecExtract: '(_ extract %d %d)',
        BitVecConcat: 'concat',
        BitVecITE: 'ite',
        ArrayStore: 'store',
    }

    def visit_BitVecConstant(self, expression):
        assert isinstance(expression, BitVecConstant)
        if expression.size == 1:
            return '#' + bin(expression.value & expression.mask)[1:]
        else:
            return '#x%0*x' % (int(expression.size/4),
                                 expression.value & expression.mask)


    def visit_BoolConstant(self, expression):
        return expression.value and 'true' or 'false' 

    def visit_Variable(self, expression):
        return expression.name

    def visit_Operation(self, expression, *operands):
        operation = self.translation_table[type(expression)]
        if isinstance(expression, (BitVecSignExtend, BitVecZeroExtend)):
            operation = operation % expression.extend
        elif isinstance(expression, BitVecExtract):
            operation = operation % (expression.end, expression.begining)

        operands = map(lambda x: self._add_binding(*x), zip(expression.operands, operands))
        smtlib = '(%s %s)' % (operation, ' '.join(operands))
        return smtlib

    @property
    def results(self):
        raise Exception("NOOO")

    @property
    def result(self):
        output = super(TranslatorSmtlib, self).result 
        if self.use_bindings:
            for name, expr, smtlib in reversed(self._bindings):
                output = '( let ((%s %s)) %s )' % (name, smtlib, output)
        #self._bindings = []
        return output

def translate_to_smtlib(expression, **kwargs):
    translator = TranslatorSmtlib(**kwargs)
    translator.visit(expression)
    return translator.result
