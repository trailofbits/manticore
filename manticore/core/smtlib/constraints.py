import itertools
import sys

from ...utils.helpers import PickleSerializer
from .expression import (
    BitVecVariable,
    BoolVariable,
    ArrayVariable,
    Array,
    Bool,
    BitVec,
    BoolConstant,
    ArrayProxy,
    BoolEq,
    Variable,
    Constant,
)
from .visitors import GetDeclarations, TranslatorSmtlib, get_variables, simplify, replace
import logging

logger = logging.getLogger(__name__)


class ConstraintSet:
    """ Constraint Sets

        An object containing a set of constraints. Serves also as a factory for
        new variables.
    """

    def __init__(self):
        self._constraints = list()
        self._parent = None
        self._sid = 0
        self._declarations = {}
        self._child = None

    def __reduce__(self):
        return (
            self.__class__,
            (),
            {
                "_parent": self._parent,
                "_constraints": self._constraints,
                "_sid": self._sid,
                "_declarations": self._declarations,
            },
        )

    def __enter__(self):
        assert self._child is None
        self._child = self.__class__()
        self._child._parent = self
        self._child._sid = self._sid
        self._child._declarations = dict(self._declarations)
        return self._child

    def __exit__(self, ty, value, traceback):
        self._child._parent = None
        self._child = None

    def __len__(self):
        if self._parent is not None:
            return len(self._constraints) + len(self._parent)
        return len(self._constraints)

    def add(self, constraint, check=False):
        """
        Add a constraint to the set

        :param constraint: The constraint to add to the set.
        :param check: Currently unused.
        :return:
        """
        if isinstance(constraint, bool):
            constraint = BoolConstant(constraint)
        assert isinstance(constraint, Bool)
        constraint = simplify(constraint)
        # If self._child is not None this constraint set has been forked and a
        # a derived constraintset may be using this. So we can't add any more
        # constraints to this one. After the child constraintSet is deleted
        # we regain the ability to add constraints.
        if self._child is not None:
            raise Exception("ConstraintSet is frozen")

        if isinstance(constraint, BoolConstant):
            if not constraint.value:
                logger.info("Adding an impossible constant constraint")
                self._constraints = [constraint]
            else:
                return

        self._constraints.append(constraint)

        if check:
            from ...core.smtlib import solver

            if not solver.check(self):
                raise ValueError("Added an impossible constraint")

    def _get_sid(self):
        """ Returns a unique id. """
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
                logger.debug("Related variables %r", [x.name for x in related_variables])
                for constraint in list(remaining_constraints):
                    if isinstance(constraint, BoolConstant):
                        if constraint.value:
                            continue
                        else:
                            related_constraints = {constraint}
                            break

                    variables = get_variables(constraint)
                    if related_variables & variables:
                        remaining_constraints.remove(constraint)
                        related_constraints.add(constraint)
                        related_variables |= variables
                        added = True

            logger.debug(
                "Reduced %d constraints!!", number_of_constraints - len(related_constraints)
            )
        else:
            related_variables = set()
            for constraint in self.constraints:
                related_variables |= get_variables(constraint)
            related_constraints = set(self.constraints)
        return related_variables, related_constraints

    def to_string(self, related_to=None, replace_constants=True):
        related_variables, related_constraints = self.__get_related(related_to)

        if replace_constants:
            constant_bindings = {}
            for expression in self.constraints:
                if (
                    isinstance(expression, BoolEq)
                    and isinstance(expression.operands[0], Variable)
                    and isinstance(expression.operands[1], Constant)
                ):
                    constant_bindings[expression.operands[0]] = expression.operands[1]

        tmp = set()
        result = ""
        for var in related_variables:
            # FIXME
            # band aid hack around the fact that we are double declaring stuff :( :(
            if var.declaration in tmp:
                logger.warning("Variable '%s' was copied twice somewhere", var.name)
                continue
            tmp.add(var.declaration)
            result += var.declaration + "\n"

        translator = TranslatorSmtlib(use_bindings=True)
        for constraint in related_constraints:
            if replace_constants:
                if (
                    isinstance(constraint, BoolEq)
                    and isinstance(constraint.operands[0], Variable)
                    and isinstance(constraint.operands[1], Constant)
                ):
                    var = constraint.operands[0]
                    expression = constraint.operands[1]
                    expression = simplify(replace(expression, constant_bindings))
                    constraint = var == expression

            translator.visit(constraint)
        for name, exp, smtlib in translator.bindings:
            if isinstance(exp, BitVec):
                result += f"(declare-fun {name} () (_ BitVec {exp.size}))"
            elif isinstance(exp, Bool):
                result += f"(declare-fun {name} () Bool)"
            elif isinstance(exp, Array):
                result += f"(declare-fun {name} () (Array (_ BitVec {exp.index_bits}) (_ BitVec {exp.value_bits})))"
            else:
                raise Exception(f"Type not supported {exp!r}")
            result += f"(assert (= {name} {smtlib}))\n"

        constraint_str = translator.pop()
        while constraint_str is not None:
            if constraint_str != "true":
                result += f"(assert {constraint_str})\n"
            constraint_str = translator.pop()
        return result

    def _declare(self, var):
        """ Declare the variable `var` """
        if var.name in self._declarations:
            raise ValueError("Variable already declared")
        self._declarations[var.name] = var
        return var

    def get_declared_variables(self):
        """ Returns the variable expressions of this constraint set """
        return self._declarations.values()

    def get_variable(self, name):
        """ Returns the variable declared under name or None if it does not exists """
        return self._declarations.get(name)

    @property
    def declarations(self):
        """ Returns the variable expressions of this constraint set """
        declarations = GetDeclarations()
        for a in self.constraints:
            try:
                declarations.visit(a)
            except RuntimeError:
                # TODO: (defunct) move recursion management out of PickleSerializer
                if sys.getrecursionlimit() >= PickleSerializer.MAX_RECURSION:
                    raise Exception(
                        f"declarations recursion limit surpassed {PickleSerializer.MAX_RECURSION}, aborting"
                    )
                new_limit = sys.getrecursionlimit() + PickleSerializer.DEFAULT_RECURSION
                if new_limit <= PickleSerializer.DEFAULT_RECURSION:
                    sys.setrecursionlimit(new_limit)
                    return self.declarations
        return declarations.result

    @property
    def constraints(self):
        """
        :rtype tuple
        :return: All constraints represented by this and parent sets.
        """
        if self._parent is not None:
            return tuple(self._constraints) + self._parent.constraints
        return tuple(self._constraints)

    def __iter__(self):
        return iter(self.constraints)

    def __str__(self):
        """ Returns a smtlib representation of the current state """
        return self.to_string()

    def _make_unique_name(self, name="VAR"):
        """ Makes a unique variable name"""
        # the while loop is necessary because appending the result of _get_sid()
        # is not guaranteed to make a unique name on the first try; a colliding
        # name could have been added previously
        while name in self._declarations:
            name = f"{name}_{self._get_sid()}"
        return name

    def is_declared(self, expression_var):
        """ True if expression_var is declared in this constraint set """
        if not isinstance(expression_var, Variable):
            raise ValueError(f"Expression must be a Variable (not a {type(expression_var)})")
        return any(expression_var is x for x in self.get_declared_variables())

    def migrate(self, expression, name_migration_map=None):
        """ Migrate an expression created for a different constraint set to self.
            Returns an expression that can be used with this constraintSet

            All the foreign variables used in the expression are replaced by
            variables of this constraint set. If the variable was replaced before
            the replacement is taken from the provided migration map.

            The migration mapping is updated with new replacements.

            :param expression: the potentially foreign expression
            :param name_migration_map: mapping of already migrated variables. maps from string name of foreign variable to its currently existing migrated string name. this is updated during this migration.
            :return: a migrated expression where all the variables are local. name_migration_map is updated

        """
        if name_migration_map is None:
            name_migration_map = {}

        #  name_migration_map -> object_migration_map
        #  Based on the name mapping in name_migration_map build an object to
        #  object mapping to be used in the replacing of variables
        #  inv: object_migration_map's keys should ALWAYS be external/foreign
        #  expressions, and its values should ALWAYS be internal/local expressions
        object_migration_map = {}

        # List of foreign vars used in expression
        foreign_vars = itertools.filterfalse(self.is_declared, get_variables(expression))
        for foreign_var in foreign_vars:
            # If a variable with the same name was previously migrated
            if foreign_var.name in name_migration_map:
                migrated_name = name_migration_map[foreign_var.name]
                native_var = self.get_variable(migrated_name)
                assert (
                    native_var is not None
                ), "name_migration_map contains a variable that does not exist in this ConstraintSet"
                object_migration_map[foreign_var] = native_var
            else:
                # foreign_var was not found in the local declared variables nor
                # any variable with the same name was previously migrated
                # let's make a new unique internal name for it
                migrated_name = foreign_var.name
                if migrated_name in self._declarations:
                    migrated_name = self._make_unique_name(f"{foreign_var.name}_migrated")
                # Create and declare a new variable of given type
                if isinstance(foreign_var, Bool):
                    new_var = self.new_bool(name=migrated_name)
                elif isinstance(foreign_var, BitVec):
                    new_var = self.new_bitvec(foreign_var.size, name=migrated_name)
                elif isinstance(foreign_var, Array):
                    # Note that we are discarding the ArrayProxy encapsulation
                    new_var = self.new_array(
                        index_max=foreign_var.index_max,
                        index_bits=foreign_var.index_bits,
                        value_bits=foreign_var.value_bits,
                        name=migrated_name,
                    ).array
                else:
                    raise NotImplemented(
                        f"Unknown expression type {type(var)} encountered during expression migration"
                    )
                # Update the var to var mapping
                object_migration_map[foreign_var] = new_var
                # Update the name to name mapping
                name_migration_map[foreign_var.name] = new_var.name

        #  Actually replace each appearance of migrated variables by the new ones
        migrated_expression = replace(expression, object_migration_map)
        return migrated_expression

    def new_bool(self, name=None, taint=frozenset(), avoid_collisions=False):
        """ Declares a free symbolic boolean in the constraint store
            :param name: try to assign name to internal variable representation,
                         if not unique, a numeric nonce will be appended
            :param avoid_collisions: potentially avoid_collisions the variable to avoid name collisions if True
            :return: a fresh BoolVariable
        """
        if name is None:
            name = "B"
            avoid_collisions = True
        if avoid_collisions:
            name = self._make_unique_name(name)
        if not avoid_collisions and name in self._declarations:
            raise ValueError(f"Name {name} already used")
        var = BoolVariable(name, taint=taint)
        return self._declare(var)

    def new_bitvec(self, size, name=None, taint=frozenset(), avoid_collisions=False):
        """ Declares a free symbolic bitvector in the constraint store
            :param size: size in bits for the bitvector
            :param name: try to assign name to internal variable representation,
                         if not unique, a numeric nonce will be appended
            :param avoid_collisions: potentially avoid_collisions the variable to avoid name collisions if True
            :return: a fresh BitVecVariable
        """
        if not (size == 1 or size % 8 == 0):
            raise Exception(f"Invalid bitvec size {size}")
        if name is None:
            name = "BV"
            avoid_collisions = True
        if avoid_collisions:
            name = self._make_unique_name(name)
        if not avoid_collisions and name in self._declarations:
            raise ValueError(f"Name {name} already used")
        var = BitVecVariable(size, name, taint=taint)
        return self._declare(var)

    def new_array(
        self,
        index_bits=32,
        name=None,
        index_max=None,
        value_bits=8,
        taint=frozenset(),
        avoid_collisions=False,
        default=None,
    ):
        """ Declares a free symbolic array of value_bits long bitvectors in the constraint store.
            :param index_bits: size in bits for the array indexes one of [32, 64]
            :param value_bits: size in bits for the array values
            :param name: try to assign name to internal variable representation,
                         if not unique, a numeric nonce will be appended
            :param index_max: upper limit for indexes on this array (#FIXME)
            :param avoid_collisions: potentially avoid_collisions the variable to avoid name collisions if True
            :param default: default for not initialized values
            :return: a fresh ArrayProxy
        """
        if name is None:
            name = "A"
            avoid_collisions = True
        if avoid_collisions:
            name = self._make_unique_name(name)
        if not avoid_collisions and name in self._declarations:
            raise ValueError(f"Name {name} already used")
        var = self._declare(ArrayVariable(index_bits, index_max, value_bits, name, taint=taint))
        return ArrayProxy(var, default=default)
