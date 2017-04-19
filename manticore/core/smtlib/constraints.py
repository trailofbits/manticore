from expression import BitVecVariable, BoolVariable, ArrayVariable, Array, Bool, BitVec, BitVecConstant, BoolConstant, ArrayProxy
from visitors import GetDeclarations, TranslatorSmtlib, ArithmeticSimplifier, PrettyPrinter, pretty_print, translate_to_smtlib, get_depth, get_variables, arithmetic_simplifier
import logging, weakref
logger = logging.getLogger('SMT')

class ConstraintSet(object):
    ''' Constraint Sets

        An object containing a set of constraints. Serves also as a factory for
        new variables.
    '''
    def __init__(self):
        self._constraints = list()
        self._parent = None
        self._sid = 0
        self._child = None


    def __reduce__(self):
        return (self.__class__, ( ), {'_parent': self._parent, '_constraints': self._constraints, '_sid':self._sid} )

    def __enter__(self):
        assert self._child is None
        self._child = self.__class__()
        self._child._parent = self
        self._child._sid = self._sid
        return self._child

    def __exit__(self, ty, value, traceback):
        self._child._parent = None
        self._child = None

        
    def __len__(self):
        if self._parent is not None:
            return len(self._constraints) + len(self._parent)
        return len(self._constraints)

    def add(self, constraint, check=False):
        '''
        Add a constraint to the set

        :param constraint: The constraint to add to the set.
        :param check: Currently unused.
        :return:
        '''
        # XXX(yan): check is an unused param
        if isinstance(constraint, bool):
            constraint = BoolConstant(constraint)
        assert isinstance(constraint, Bool)
        constraint = arithmetic_simplifier(constraint)
        # If count > 0 it means this constraint set has been forked and that 
        # a derived constraintset may be using this. So we can't add any more
        # constraints to this one. After the child constraintSet is deleted
        # we regain the ability to add constraints.
        if self._child is not None:
            raise Exception('ConstraintSet is frozen')
        self._constraints.append(constraint)

    def _get_sid(self):
        ''' Returns an unique id. '''
        assert self._child is None
        self._sid += 1
        return self._sid

    def related_to(self, expression):
        if isinstance(expression, BoolConstant) and expression.value is True:
            return str(self)

        N = len(self.constraints)
        related_variables = get_variables(expression)
        related_constraints = set()
        remaining_constraints = set(self.constraints)

        added = True
        while added:
            added = False
            logger.debug('Related variables %r', map(lambda x: x.name, related_variables))
            for constraint in list(remaining_constraints):
                variables = get_variables(constraint)
                if related_variables & variables:
                    remaining_constraints.remove(constraint)
                    related_constraints.add(constraint)
                    related_variables |= variables
                    added = True
                    
        result = ''
        for var in related_variables:
            result += var.declaration + '\n'
#        for prop in related_constraints:
#            result += '(assert %s)\n' % translate_to_smtlib(prop, bindings=True)

        translator = TranslatorSmtlib(use_bindings=True)
        for expression in related_constraints:
            translator.visit(expression)

        for name, exp, smtlib in translator.bindings:
            if isinstance(exp, BitVec):
                result += '(declare-fun %s () (_ BitVec %d))'%(name, exp.size)
            elif isinstance(exp, Bool):
                result += '(declare-fun %s () Bool)' % name
            elif isinstance(exp, Array):
                result += '(declare-fun %s () (Array (_ BitVec %d) (_ BitVec 8)))' % (name, exp.index_bits)
            else:
                raise Exception("Type not supported %r", exp)
            result += '(assert (= %s %s))\n' % (name, smtlib)

        r = translator.pop()
        while r is not None:
            result += '(assert %s)\n' % r
            r = translator.pop()

        logger.debug('Reduced %d constraints!!', N - len(related_constraints))

        return result
        #return str(self) #//result

    @property
    def declarations(self):
        declarations = GetDeclarations()
        for a in self.constraints:
            try:
                declarations.visit(a)
            except:
                # there recursion limit exceeded problem, 
                # try a slower, iterative solution
                #logger.info('WARNING: using iterpickle to dump recursive expression')
                #from utils import iterpickle
                #file('recursive.pkl', 'w').write(iterpickle.dumps(a))
                raise
        return declarations.result

    @property
    def constraints(self):
        '''
        :rtype tuple
        :return: All constraints represented by this and parent sets.
        '''
        if self._parent is not None:
            return tuple(self._constraints) + self._parent.constraints
        return tuple(self._constraints)

    def __str__(self):
        ''' Returns a smtlib representation of the current state '''
        result = ''
        translator = TranslatorSmtlib(use_bindings=True)
        for expression in self.constraints:
            translator.visit(expression)

        for d in self.declarations:
            result += d.declaration + '\n'

        for name, exp, smtlib in translator.bindings:
            if isinstance(exp, BitVec):
                result += '(declare-fun %s () (_ BitVec %d))'%(name, exp.size)
            elif isinstance(exp, Bool):
                result += '(declare-fun %s () Bool)' % name
            elif isinstance(exp, Array):
                result += '(declare-fun %s () (Array (_ BitVec %d) (_ BitVec 8)))' % (name, exp.index_bits)
            else:
                raise Exception("Type not supported %r", exp)
            result += '(assert (= %s %s))\n' % (name, smtlib)

        r = translator.pop()
        while r is not None:
            result += '(assert %s)\n' % r
            r = translator.pop()

        return result

        buf = ''
        for d in self.declarations:
            buf += d.declaration + '\n'
        for a in self.constraints:
            buf += '(assert %s)\n' % translate_to_smtlib(a, use_bindings=True)
        return buf

    def _get_new_name(self, name='VAR'):
        ''' Makes an uniq variable name'''
        return '%s_%d' % (name, self._get_sid())

    def new_bool(self, name='B', taint=frozenset()):
        ''' Declares a free symbolic boolean in the constraint store
            :param name: try to assign name to internal variable representation,
                         if not uniq a numeric nonce will be appended
            :return: a fresh BoolVariable
        '''
        name = self._get_new_name(name)
        return BoolVariable(name, taint=taint)

    def new_bitvec(self, size, name='V', taint=frozenset()):
        ''' Declares a free symbolic bitvector in the constraint store
            :param size: size in bits for the bitvector
            :param name: try to assign name to internal variable representation,
                         if not uniq a numeric nonce will be appended
            :return: a fresh BitVecVariable
        '''
        assert size in (1, 4, 8, 16, 32, 64, 128, 256)
        name = self._get_new_name(name)
        return BitVecVariable(size, name, taint=taint)

    def new_array(self, index_bits=32, name='A', index_max=None, taint=frozenset()):
        ''' Declares a free symbolic array of 8 bits long bitvectors in the constraint store.
            :param index_bit_size: size in bits for the array indexes one of [32, 64]
            :param name: try to assign name to internal variable representation,
                         if not uniq a numeric nonce will be appended
            :param index_max: upper limit for indexes on ths array (#FIXME)
            :return: a fresh BitVecVariable
        '''
        assert index_bits in (8, 16, 32, 64)
        name = self._get_new_name(name)
        return ArrayProxy(ArrayVariable(index_bits, index_max, name, taint=taint))


