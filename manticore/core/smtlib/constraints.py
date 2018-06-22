from __future__ import absolute_import
from .expression import BitVecVariable, BoolVariable, ArrayVariable, Array, Bool, BitVec, BoolConstant, ArrayProxy, BoolEq, Variable, Constant
from .visitors import GetDeclarations, TranslatorSmtlib, get_variables, simplify, replace
import logging

logger = logging.getLogger(__name__)


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
        return (self.__class__, (), {'_parent': self._parent, '_constraints': self._constraints, '_sid': self._sid})

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
        constraint = simplify(constraint)
        # If self._child is not None this constraint set has been forked and a
        # a derived constraintset may be using this. So we can't add any more
        # constraints to this one. After the child constraintSet is deleted
        # we regain the ability to add constraints.
        if self._child is not None:
            raise Exception('ConstraintSet is frozen')

        if isinstance(constraint, BoolConstant):
            if not constraint.value:
                logger.info("Adding an imposible constant constraint")
                self._constraints = [constraint]
            else:
                return

        self._constraints.append(constraint)

    def _get_sid(self):
        ''' Returns an unique id. '''
        assert self._child is None
        self._sid += 1
        return self._sid

    def __get_related(self, related_to=None):
        if related_to is not None:
            number_of_constraints = len(self.constraints)
            remaining_constraints = set(self.constraints)
            related_variables = get_variables(related_to)
            related_constraints = set()

            added = True
            while added:
                added = False
                logger.debug('Related variables %r', map(lambda x: x.name, related_variables))
                for constraint in list(remaining_constraints):
                    if isinstance(constraint, BoolConstant):
                        if constraint.value:
                            continue
                        else:
                            related_constraints = set((constraint,))
                            break

                    variables = get_variables(constraint)
                    if related_variables & variables:
                        remaining_constraints.remove(constraint)
                        related_constraints.add(constraint)
                        related_variables |= variables
                        added = True

            logger.debug('Reduced %d constraints!!', number_of_constraints - len(related_constraints))
        else:
            related_variables = set()
            for constraint in self.constraints:
                related_variables |= get_variables(constraint)
            related_constraints = set(self.constraints)

        return related_variables, related_constraints

    def to_string(self, related_to=None, replace_constants=False):
        replace_constants = True
        related_variables, related_constraints = self.__get_related(related_to)

        if replace_constants:
            constant_bindings = {}
            for expression in self.constraints:
                if isinstance(expression, BoolEq) and \
                   isinstance(expression.operands[0], Variable) and \
                   isinstance(expression.operands[1], Constant):
                    constant_bindings[expression.operands[0]] = expression.operands[1]

        tmp = set()
        result = ''
        for var in related_variables:
            # FIXME
            # band aid hack around the fact that we are double declaring stuff :( :(
            if var.declaration in tmp:
                logger.warning("Variable '%s' was copied twice somewhere", var.name)
                continue
            tmp.add(var.declaration)
            result += var.declaration + '\n'

        translator = TranslatorSmtlib(use_bindings=True)
        for constraint in related_constraints:
            if replace_constants:
                constraint = simplify(replace(constraint, constant_bindings))
            translator.visit(constraint)

        for name, exp, smtlib in translator.bindings:
            if isinstance(exp, BitVec):
                result += '(declare-fun %s () (_ BitVec %d))' % (name, exp.size)
            elif isinstance(exp, Bool):
                result += '(declare-fun %s () Bool)' % name
            elif isinstance(exp, Array):
                result += '(declare-fun %s () (Array (_ BitVec %d) (_ BitVec %d)))' % (name, exp.index_bits, exp.value_bits)
            else:
                raise Exception("Type not supported %r", exp)
            result += '(assert (= %s %s))\n' % (name, smtlib)

        constraint_str = translator.pop()
        while constraint_str is not None:
            if constraint_str != 'true':
                result += '(assert %s)\n' % constraint_str
            constraint_str = translator.pop()
        return result

    @property
    def declarations(self):
        declarations = GetDeclarations()
        for a in self.constraints:
            try:
                declarations.visit(a)
            except BaseException:
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

    def __iter__(self):
        return iter(self.constraints)

    def __str__(self):
        ''' Returns a smtlib representation of the current state '''
        return self.to_string()

    def _get_new_name(self, name='VAR'):
        ''' Makes an uniq variable name'''
        return '%s_%d' % (name, self._get_sid())

    def migrate(self, expression, name=None, bindings=None):
        ''' Migrate an expression created for a different constraint set
            Returns an expression that can be used with this constraintSet
        '''
        # Simply check there are no name overlappings
        if bindings is None:
            bindings = {}
        if name is None:
            name = self._get_new_name('migrated')
        variables = get_variables(expression)
        for var in variables:
            if var in bindings:
                continue
            if isinstance(var, Bool):
                new_var = self.new_bool()
            elif isinstance(expression, BitVec):
                new_var = self.new_bitvec(var.size)
            elif isinstance(expression, Array):
                new_var = self.new_array(index_max=var.index_max, index_bits=var.index_bits, value_bits=var.value_bits)
            bindings[var] = new_var

        return replace(expression, bindings)

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
        if not (size == 1 or size % 8 == 0):
            raise Exception('Invalid bitvec size %s' % size)
        name = self._get_new_name(name)
        return BitVecVariable(size, name, taint=taint)

    def new_array(self, index_bits=32, name='A', index_max=None, value_bits=8, taint=frozenset()):
        ''' Declares a free symbolic array of value_bits long bitvectors in the constraint store.
            :param index_bits: size in bits for the array indexes one of [32, 64]
            :param value_bits: size in bits for the array values
            :param name: try to assign name to internal variable representation,
                         if not uniq a numeric nonce will be appended
            :param index_max: upper limit for indexes on ths array (#FIXME)
            :return: a fresh ArrayProxy
        '''
        name = self._get_new_name(name)
        return ArrayProxy(ArrayVariable(index_bits, index_max, value_bits, name, taint=taint))
