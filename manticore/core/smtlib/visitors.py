from ...utils.helpers import CacheDict
from .expression import *
from functools import lru_cache
import logging
import operator

logger = logging.getLogger(__name__)


class Visitor:
    """ Class/Type Visitor

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

        visit_Constant()
        visit_Variable()
        visit_Operation()
        visit_BitVec()
        visit_Bool()
        visit_Array()

    """

    def __init__(self, cache=None, **kwargs):
        super().__init__()
        self._stack = []
        self._cache = {} if cache is None else cache

    def push(self, value):
        assert value is not None
        self._stack.append(value)

    def pop(self):
        if len(self._stack) == 0:
            return None
        result = self._stack.pop()
        return result

    @property
    def result(self):
        assert len(self._stack) == 1
        return self._stack[-1]

    def _method(self, expression, *args):
        assert expression.__class__.__mro__[-1] is object
        for cls in expression.__class__.__mro__:
            sort = cls.__name__
            methodname = "visit_%s" % sort
            if hasattr(self, methodname):
                value = getattr(self, methodname)(expression, *args)
                if value is not None:
                    assert isinstance(value, Expression)
                    return value
        return self._rebuild(expression, args)

    def visit(self, node, use_fixed_point=False):
        """
        The entry point of the visitor.
        The exploration algorithm is a DFS post-order traversal
        The implementation used two stacks instead of a recursion
        The final result is store in self.result

        :param node: Node to explore
        :type node: Expression
        :param use_fixed_point: if True, it runs _methods until a fixed point is found
        :type use_fixed_point: Bool
        """
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
                    operands = [self.pop() for _ in range(len(node.operands))]
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

        if use_fixed_point:
            old_value = None
            new_value = self.pop()
            while old_value is not new_value:
                self.visit(new_value)
                old_value = new_value
                new_value = self.pop()
            self.push(new_value)

    @staticmethod
    def _rebuild(expression, operands):
        if isinstance(expression, Operation):
            if any(x is not y for x, y in zip(expression.operands, operands)):
                import copy

                aux = copy.copy(expression)
                aux._operands = operands
                return aux
        return expression


class Translator(Visitor):
    """ Simple visitor to translate an expression into something else
    """

    def _method(self, expression, *args):
        # Special case. Need to get the unsleeved version of the array
        if isinstance(expression, ArrayProxy):
            expression = expression.array
        assert expression.__class__.__mro__[-1] is object
        for cls in expression.__class__.__mro__:
            sort = cls.__name__
            methodname = f"visit_{sort:s}"
            if hasattr(self, methodname):
                value = getattr(self, methodname)(expression, *args)
                if value is not None:
                    return value
        raise Exception(f"No translation for this {expression}")


class GetDeclarations(Visitor):
    """ Simple visitor to collect all variables in an expression or set of
        expressions
    """

    def __init__(self, **kwargs):
        super().__init__(**kwargs)
        self.variables = set()

    def visit_Variable(self, expression):
        self.variables.add(expression)

    @property
    def result(self):
        return self.variables


class GetDepth(Translator):
    """ Simple visitor to collect all variables in an expression or set of
        expressions
    """

    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)

    def visit_Expression(self, expression):
        return 1

    def visit_Operation(self, expression, *operands):
        return 1 + max(operands)


def get_depth(exp):
    visitor = GetDepth()
    visitor.visit(exp)
    return visitor.result


class PrettyPrinter(Visitor):
    def __init__(self, depth=None, **kwargs):
        super().__init__(**kwargs)
        self.output = ""
        self.indent = 0
        self.depth = depth

    def _print(self, s, e=None):
        self.output += " " * self.indent + str(s)  # + '(%016x)'%hash(e)
        self.output += "\n"

    def visit(self, expression):
        """
        Overload Visitor.visit because:
        - We need a pre-order traversal
        - We use a recursion as it makes it easier to keep track of the indentation

        """
        self._method(expression)

    def _method(self, expression, *args):
        """
        Overload Visitor._method because we want to stop to iterate over the
        visit_ functions as soon as a valid visit_ function is found
        """
        assert expression.__class__.__mro__[-1] is object
        for cls in expression.__class__.__mro__:
            sort = cls.__name__
            methodname = "visit_%s" % sort
            method = getattr(self, methodname, None)
            if method is not None:
                method(expression, *args)
                return
        return

    def visit_Operation(self, expression, *operands):
        self._print(expression.__class__.__name__, expression)
        self.indent += 2
        if self.depth is None or self.indent < self.depth * 2:
            for o in expression.operands:
                self.visit(o)
        else:
            self._print("...")
        self.indent -= 2
        return ""

    def visit_BitVecExtract(self, expression):
        self._print(
            expression.__class__.__name__ + "{%d:%d}" % (expression.begining, expression.end),
            expression,
        )
        self.indent += 2
        if self.depth is None or self.indent < self.depth * 2:
            for o in expression.operands:
                self.visit(o)
        else:
            self._print("...")
        self.indent -= 2
        return ""

    def visit_Constant(self, expression):
        self._print(expression.value)
        return ""

    def visit_Variable(self, expression):
        self._print(expression.name)
        return ""

    @property
    def result(self):
        return self.output


def pretty_print(expression, **kwargs):
    if not isinstance(expression, Expression):
        return str(expression)
    pp = PrettyPrinter(**kwargs)
    pp.visit(expression)
    return pp.result


class ConstantFolderSimplifier(Visitor):
    def __init__(self, **kw):
        super().__init__(**kw)

    operations = {
        BitVecAdd: operator.__add__,
        BitVecSub: operator.__sub__,
        BitVecMul: operator.__mul__,
        BitVecDiv: operator.__truediv__,
        BitVecShiftLeft: operator.__lshift__,
        BitVecShiftRight: operator.__rshift__,
        BitVecAnd: operator.__and__,
        BitVecOr: operator.__or__,
        BitVecXor: operator.__xor__,
        BitVecNot: operator.__not__,
        BitVecNeg: operator.__invert__,
        LessThan: operator.__lt__,
        LessOrEqual: operator.__le__,
        Equal: operator.__eq__,
        GreaterThan: operator.__gt__,
        GreaterOrEqual: operator.__ge__,
        BoolAnd: operator.__and__,
        BoolOr: operator.__or__,
        BoolNot: operator.__not__,
    }

    def visit_BitVecConcat(self, expression, *operands):
        if all(isinstance(o, Constant) for o in operands):
            result = 0
            for o in operands:
                result <<= o.size
                result |= o.value
            return BitVecConstant(expression.size, result, taint=expression.taint)

    def visit_BitVecZeroExtend(self, expression, *operands):
        if all(isinstance(o, Constant) for o in operands):
            return BitVecConstant(expression.size, operands[0].value, taint=expression.taint)

    def visit_BitVecSignExtend(self, expression, *operands):
        if expression.extend == 0:
            return operands[0]

    def visit_BitVecExtract(self, expression, *operands):
        if all(isinstance(o, Constant) for o in expression.operands):
            value = expression.operands[0].value
            begining = expression.begining
            end = expression.end
            value = value >> begining
            mask = 2 ** (end - begining + 1) - 1
            value = value & mask
            return BitVecConstant(expression.size, value, taint=expression.taint)

    def visit_BoolAnd(self, expression, a, b):
        if isinstance(a, Constant) and a.value == True:
            return b
        if isinstance(b, Constant) and b.value == True:
            return a

    def visit_BoolOr(self, expression, a, b):
        if isinstance(a, Constant) and a.value == False:
            return b
        if isinstance(b, Constant) and b.value == False:
            return a

    def visit_Operation(self, expression, *operands):
        """ constant folding, if all operands of an expression are a Constant do the math """
        operation = self.operations.get(type(expression), None)
        if operation is not None and all(isinstance(o, Constant) for o in operands):
            value = operation(*(x.value for x in operands))
            if isinstance(expression, BitVec):
                return BitVecConstant(expression.size, value, taint=expression.taint)
            else:
                isinstance(expression, Bool)
                return BoolConstant(value, taint=expression.taint)
        else:
            if any(operands[i] is not expression.operands[i] for i in range(len(operands))):
                expression = self._rebuild(expression, operands)
        return expression


constant_folder_simplifier_cache = CacheDict(max_size=150000, flush_perc=25)


@lru_cache(maxsize=128)
def constant_folder(expression):
    global constant_folder_simplifier_cache
    simp = ConstantFolderSimplifier(cache=constant_folder_simplifier_cache)
    simp.visit(expression, use_fixed_point=True)
    return simp.result


class ArithmeticSimplifier(Visitor):
    def __init__(self, parent=None, **kw):
        super().__init__(**kw)

    @staticmethod
    def _same_constant(a, b):
        return isinstance(a, Constant) and isinstance(b, Constant) and a.value == b.value or a is b

    @staticmethod
    def _changed(expression, operands):
        if isinstance(expression, Constant) and len(operands) > 0:
            return True
        arity = len(operands)
        return any(operands[i] is not expression.operands[i] for i in range(arity))

    def visit_Operation(self, expression, *operands):
        """ constant folding, if all operands of an expression are a Constant do the math """
        if all(isinstance(o, Constant) for o in operands):
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
        # FIXME Enable some taint propagating optimization
        if isinstance(expression.operands[0], Constant) and not expression.operands[0].taint:
            if expression.operands[0].value:
                result = expression.operands[1]
            else:
                result = expression.operands[2]
            return result

        if self._changed(expression, operands):
            return BitVecITE(expression.size, *operands, taint=expression.taint)

    def visit_BitVecConcat(self, expression, *operands):
        """ concat( extract(k1, 0, a), extract(sizeof(a)-k1, k1, a))  ==> a
            concat( extract(k1, beg, a), extract(end, k1, a))  ==> extract(beg, end, a)
        """
        op = expression.operands[0]

        value = None
        end = None
        begining = None
        for o in operands:
            # If found a non BitVecExtract, do not apply
            if not isinstance(o, BitVecExtract):
                return None
            # Set the value for the first item
            if value is None:
                value = o.value
                begining = o.begining
                end = o.end
            else:
                # If concat of extracts of different values do not apply
                if value is not o.value:
                    return None
                # If concat of non contiguous extracs do not apply
                if begining != o.end + 1:
                    return None
                # update begining variable
                begining = o.begining

        if value is not None:
            if end + 1 == value.size and begining == 0:
                return value
            else:
                return BitVecExtract(value, begining, end - begining + 1, taint=expression.taint)

    def visit_BitVecExtract(self, expression, *operands):
        """ extract(sizeof(a), 0)(a)  ==> a
            extract(16, 0)( concat(a,b,c,d) ) => concat(c, d)
            extract(m,M)(and/or/xor a b ) => and/or/xor((extract(m,M) a) (extract(m,M) a)
        """
        op = expression.operands[0]
        begining = expression.begining
        end = expression.end
        size = end - begining + 1

        # extract(sizeof(a), 0)(a)  ==> a
        if begining == 0 and end + 1 == op.size:
            return op
        elif isinstance(op, BitVecExtract):
            return BitVecExtract(op.value, op.begining + begining, size, taint=expression.taint)
        elif isinstance(op, BitVecConcat):
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
                return BitVecExtract(
                    BitVecConcat(sum([x.size for x in new_operands]), *reversed(new_operands)),
                    begining,
                    expression.size,
                    taint=expression.taint,
                )
        if isinstance(op, (BitVecAnd, BitVecOr, BitVecXor)):
            bitoperand_a, bitoperand_b = op.operands
            return op.__class__(
                BitVecExtract(bitoperand_a, begining, expression.size),
                BitVecExtract(bitoperand_b, begining, expression.size),
                taint=expression.taint,
            )

    def visit_BitVecAdd(self, expression, *operands):
        """ a + 0  ==> a
            0 + a  ==> a
        """
        left = expression.operands[0]
        right = expression.operands[1]
        if isinstance(right, BitVecConstant):
            if right.value == 0:
                return left
        if isinstance(left, BitVecConstant):
            if left.value == 0:
                return right

    def visit_BitVecSub(self, expression, *operands):
        """ a - 0 ==> 0
            (a + b) - b  ==> a
            (b + a) - b  ==> a
        """
        left = expression.operands[0]
        right = expression.operands[1]
        if isinstance(left, BitVecAdd):
            if self._same_constant(left.operands[0], right):
                return left.operands[1]
            elif self._same_constant(left.operands[1], right):
                return left.operands[0]
        elif isinstance(left, BitVecSub) and isinstance(right, Constant):
            subleft = left.operands[0]
            subright = left.operands[1]
            if isinstance(subright, Constant):
                return BitVecSub(
                    subleft,
                    BitVecConstant(
                        subleft.size,
                        subright.value + right.value,
                        taint=subright.taint | right.taint,
                    ),
                )

    def visit_BitVecOr(self, expression, *operands):
        """ a | 0 => a
            0 | a => a
            0xffffffff & a => 0xffffffff
            a & 0xffffffff => 0xffffffff

        """
        left = expression.operands[0]
        right = expression.operands[1]
        if isinstance(right, BitVecConstant):
            if right.value == 0:
                return left
            elif right.value == left.mask:
                return right
            elif isinstance(left, BitVecOr):
                left_left = left.operands[0]
                left_right = left.operands[1]
                if isinstance(right, Constant):
                    return BitVecOr(left_left, (left_right | right), taint=expression.taint)
        elif isinstance(left, BitVecConstant):
            return BitVecOr(right, left, taint=expression.taint)

    def visit_BitVecAnd(self, expression, *operands):
        """ ct & x => x & ct                move constants to the right
            a & 0 => 0                      remove zero
            a & 0xffffffff => a             remove full mask
            (b & ct2) & ct => b & (ct&ct2)  associative property
            (a & (b | c) => a&b | a&c       distribute over |
        """
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
                    return BitVecAnd(left_left, left_right & right, taint=expression.taint)
            elif isinstance(left, BitVecOr):
                left_left = left.operands[0]
                left_right = left.operands[1]
                return BitVecOr(right & left_left, right & left_right, taint=expression.taint)

        elif isinstance(left, BitVecConstant):
            return BitVecAnd(right, left, taint=expression.taint)

    def visit_BitVecShiftLeft(self, expression, *operands):
        """ a << 0 => a                       remove zero
            a << ct => 0 if ct > sizeof(a)    remove big constant shift
        """
        left = expression.operands[0]
        right = expression.operands[1]
        if isinstance(right, BitVecConstant):
            if right.value == 0:
                return left
            elif right.value >= right.size:
                return left

    def visit_ArraySelect(self, expression, *operands):
        """ ArraySelect (ArrayStore((ArrayStore(x0,v0) ...),xn, vn), x0)
                -> v0
        """
        arr, index = operands
        if isinstance(arr, ArrayVariable):
            return

        if isinstance(index, BitVecConstant):
            ival = index.value

            # props are slow and using them in tight loops should be avoided, esp when they offer no additional validation
            # arr._operands[1] = arr.index, arr._operands[0] = arr.array
            while (
                isinstance(arr, ArrayStore)
                and isinstance(arr._operands[1], BitVecConstant)
                and arr._operands[1]._value != ival
            ):
                arr = arr._operands[0]  # arr.array

        if (
            isinstance(index, BitVecConstant)
            and isinstance(arr, ArrayStore)
            and isinstance(arr.index, BitVecConstant)
            and arr.index.value == index.value
        ):
            return arr.value
        else:
            if arr is not expression.array:
                return arr.select(index)

    def visit_Expression(self, expression, *operands):
        assert len(operands) == 0
        assert not isinstance(expression, Operation)
        return expression


arithmetic_simplifier_cache = CacheDict(max_size=150000, flush_perc=25)


@lru_cache(maxsize=128)
def arithmetic_simplify(expression):
    global arithmetic_simplifier_cache
    simp = ArithmeticSimplifier(cache=arithmetic_simplifier_cache)
    simp.visit(expression, use_fixed_point=True)
    return simp.result


def to_constant(expression):
    """
        Iff the expression can be simplified to a Constant get the actual concrete value.
        This discards/ignore any taint
    """
    value = simplify(expression)
    if isinstance(value, Expression) and value.taint:
        raise ValueError("Can not simplify tainted values to constant")
    if isinstance(value, Constant):
        return value.value
    elif isinstance(value, Array):
        if expression.index_max:
            ba = bytearray()
            for i in range(expression.index_max):
                value_i = simplify(value[i])
                if not isinstance(value_i, Constant):
                    break
                ba.append(value_i.value)
            else:
                return bytes(ba)
            return expression
    return value


@lru_cache(maxsize=128)
def simplify(expression):
    expression = constant_folder(expression)
    expression = arithmetic_simplify(expression)
    return expression


class TranslatorSmtlib(Translator):
    """ Simple visitor to translate an expression to its smtlib representation
    """

    unique = 0

    def __init__(self, use_bindings=False, *args, **kw):
        assert "bindings" not in kw
        super().__init__(*args, **kw)
        self.use_bindings = use_bindings
        self._bindings_cache = {}
        self._bindings = []

    def _add_binding(self, expression, smtlib):
        if not self.use_bindings or len(smtlib) <= 10:
            return smtlib

        if smtlib in self._bindings_cache:
            return self._bindings_cache[smtlib]

        TranslatorSmtlib.unique += 1
        name = "a_%d" % TranslatorSmtlib.unique

        self._bindings.append((name, expression, smtlib))

        self._bindings_cache[expression] = name
        return name

    @property
    def bindings(self):
        return self._bindings

    translation_table = {
        BoolNot: "not",
        BoolEq: "=",
        BoolAnd: "and",
        BoolOr: "or",
        BoolXor: "xor",
        BoolITE: "ite",
        BitVecAdd: "bvadd",
        BitVecSub: "bvsub",
        BitVecMul: "bvmul",
        BitVecDiv: "bvsdiv",
        BitVecUnsignedDiv: "bvudiv",
        BitVecMod: "bvsmod",
        BitVecRem: "bvsrem",
        BitVecUnsignedRem: "bvurem",
        BitVecShiftLeft: "bvshl",
        BitVecShiftRight: "bvlshr",
        BitVecArithmeticShiftLeft: "bvashl",
        BitVecArithmeticShiftRight: "bvashr",
        BitVecAnd: "bvand",
        BitVecOr: "bvor",
        BitVecXor: "bvxor",
        BitVecNot: "bvnot",
        BitVecNeg: "bvneg",
        LessThan: "bvslt",
        LessOrEqual: "bvsle",
        Equal: "=",
        GreaterThan: "bvsgt",
        GreaterOrEqual: "bvsge",
        UnsignedLessThan: "bvult",
        UnsignedLessOrEqual: "bvule",
        UnsignedGreaterThan: "bvugt",
        UnsignedGreaterOrEqual: "bvuge",
        BitVecSignExtend: "(_ sign_extend %d)",
        BitVecZeroExtend: "(_ zero_extend %d)",
        BitVecExtract: "(_ extract %d %d)",
        BitVecConcat: "concat",
        BitVecITE: "ite",
        ArrayStore: "store",
        ArraySelect: "select",
    }

    def visit_BitVecConstant(self, expression):
        assert isinstance(expression, BitVecConstant)
        if expression.size == 1:
            return "#" + bin(expression.value & expression.mask)[1:]
        else:
            return "#x%0*x" % (int(expression.size / 4), expression.value & expression.mask)

    def visit_BoolConstant(self, expression):
        return expression.value and "true" or "false"

    def visit_Variable(self, expression):
        return expression.name

    def visit_ArraySelect(self, expression, *operands):
        array_smt, index_smt = operands
        if isinstance(expression.array, ArrayStore):
            array_smt = self._add_binding(expression.array, array_smt)

        return "(select %s %s)" % (array_smt, index_smt)

    def visit_Operation(self, expression, *operands):
        operation = self.translation_table[type(expression)]
        if isinstance(expression, (BitVecSignExtend, BitVecZeroExtend)):
            operation = operation % expression.extend
        elif isinstance(expression, BitVecExtract):
            operation = operation % (expression.end, expression.begining)

        operands = [self._add_binding(*x) for x in zip(expression.operands, operands)]
        return "(%s %s)" % (operation, " ".join(operands))

    @property
    def results(self):
        raise Exception("NOOO")

    @property
    def result(self):
        output = super().result
        if self.use_bindings:
            for name, expr, smtlib in reversed(self._bindings):
                output = "( let ((%s %s)) %s )" % (name, smtlib, output)
        return output


def translate_to_smtlib(expression, **kwargs):
    translator = TranslatorSmtlib(**kwargs)
    translator.visit(expression)
    return translator.result


class Replace(Visitor):
    """ Simple visitor to replaces expressions """

    def __init__(self, bindings=None, **kwargs):
        super().__init__(**kwargs)
        if bindings is None:
            raise ValueError("bindings needed in replace")
        self._replace_bindings = bindings

    def visit_Variable(self, expression):
        if expression in self._replace_bindings:
            return self._replace_bindings[expression]
        return expression


def replace(expression, bindings):
    if not bindings:
        return expression
    visitor = Replace(bindings)
    visitor.visit(expression, use_fixed_point=True)
    result_expression = visitor.result
    return result_expression


class ArraySelectSimplifier(Visitor):
    class ExpressionNotSimple(RuntimeError):
        pass

    def __init__(self, target_index, **kwargs):
        super().__init__(**kwargs)
        self._target_index = target_index
        self.stores = []

    def visit_ArrayStore(self, exp, target, where, what):
        if not isinstance(what, BitVecConstant):
            raise self.ExpressionNotSimple

        if where.value == self._target_index:
            self.stores.append(what.value)


def simplify_array_select(array_exp):
    assert isinstance(array_exp, ArraySelect)
    simplifier = ArraySelectSimplifier(array_exp.index.value)
    simplifier.visit(array_exp)
    return simplifier.stores


def get_variables(expression):
    visitor = GetDeclarations()
    visitor.visit(expression)
    return visitor.result
