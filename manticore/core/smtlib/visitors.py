from ...utils.helpers import CacheDict
from ...exceptions import SmtlibError
from .expression import *
from functools import lru_cache
import copy
import logging
import operator
import math
import threading
from decimal import Decimal

logger = logging.getLogger(__name__)


class Visitor:
    """Class/Type Visitor

    Inherit your class visitor from this one and get called on a different
    visiting function for each type of expression. It will call the first
    implemented method for the __mro__ class order.
     For example for a BitVecAdd it will try
         visit_BitVecAdd()          if not defined then it will try with
         visit_BitVecOperation()    if not defined then it will try with
         visit_BitVec()             if not defined then it will try with
         visit_Expression()

     Other class named visitors are:

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
        for cls in expression.__class__.__mro__[:-1]:
            sort = cls.__name__
            methodname = "visit_%s" % sort
            if hasattr(self, methodname):
                value = getattr(self, methodname)(expression, *args)
                if value is not None:
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
        if isinstance(node, ArrayProxy):
            node = node.array
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
                aux = copy.copy(expression)
                aux._operands = operands
                return aux
        return expression


class Translator(Visitor):
    """Simple visitor to translate an expression into something else"""

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
        raise SmtlibError(f"No translation for this {expression}")


class GetDeclarations(Visitor):
    """Simple visitor to collect all variables in an expression or set of
    expressions
    """

    def __init__(self, **kwargs):
        super().__init__(**kwargs)
        self.variables = set()

    def _visit_variable(self, expression):
        self.variables.add(expression)

    visit_ArrayVariable = _visit_variable
    visit_BitVecVariable = _visit_variable
    visit_BoolVariable = _visit_variable

    @property
    def result(self):
        return self.variables


class GetDepth(Translator):
    """Simple visitor to collect all variables in an expression or set of
    expressions
    """

    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)

    def visit_Expression(self, expression):
        return 1

    def _visit_operation(self, expression, *operands):
        return 1 + max(operands)

    visit_ArraySelect = _visit_operation
    visit_ArrayOperation = _visit_operation
    visit_BoolOperation = _visit_operation
    visit_BitVecOperation = _visit_operation


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

    def _visit_operation(self, expression, *operands):
        self._print(expression.__class__.__name__, expression)
        self.indent += 2
        if self.depth is None or self.indent < self.depth * 2:
            for o in expression.operands:
                self.visit(o)
        else:
            self._print("...")
        self.indent -= 2
        return ""

    visit_ArraySelect = _visit_operation
    visit_ArrayOperation = _visit_operation
    visit_BoolOperation = _visit_operation
    visit_BitVecOperation = _visit_operation

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

    def _visit_constant(self, expression):
        self._print(expression.value)
        return ""

    visit_BitVecConstant = _visit_constant
    visit_BoolConstant = _visit_constant

    def _visit_variable(self, expression):
        self._print(expression.name)
        return ""

    visit_ArrayVariable = _visit_variable
    visit_BitVecVariable = _visit_variable
    visit_BoolVariable = _visit_variable

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
        BitVecMod: operator.__mod__,
        BitVecAdd: operator.__add__,
        BitVecSub: operator.__sub__,
        BitVecMul: operator.__mul__,
        BitVecShiftLeft: operator.__lshift__,
        BitVecShiftRight: operator.__rshift__,
        BitVecAnd: operator.__and__,
        BitVecOr: operator.__or__,
        BitVecXor: operator.__xor__,
        BitVecNot: operator.__not__,
        BitVecNeg: operator.__invert__,
        BoolAnd: operator.__and__,
        BoolEqual: operator.__eq__,
        BoolOr: operator.__or__,
        BoolNot: operator.__not__,
        UnsignedLessThan: operator.__lt__,
        UnsignedLessOrEqual: operator.__le__,
        UnsignedGreaterThan: operator.__gt__,
        UnsignedGreaterOrEqual: operator.__ge__,
    }

    def visit_BitVecUnsignedDiv(self, expression, *operands) -> Optional[BitVecConstant]:
        if all(isinstance(o, Constant) for o in operands):
            a = operands[0].value
            b = operands[1].value
            if a == 0:
                ret = 0
            else:
                ret = math.trunc(Decimal(a) / Decimal(b))
            return BitVecConstant(expression.size, ret, taint=expression.taint)
        return None

    def visit_LessThan(self, expression, *operands) -> Optional[BoolConstant]:
        if all(isinstance(o, Constant) for o in operands):
            a = operands[0].signed_value
            b = operands[1].signed_value
            return BoolConstant(a < b, taint=expression.taint)
        return None

    def visit_LessOrEqual(self, expression, *operands) -> Optional[BoolConstant]:
        if all(isinstance(o, Constant) for o in operands):
            a = operands[0].signed_value
            b = operands[1].signed_value
            return BoolConstant(a <= b, taint=expression.taint)
        return None

    def visit_GreaterThan(self, expression, *operands) -> Optional[BoolConstant]:
        if all(isinstance(o, Constant) for o in operands):
            a = operands[0].signed_value
            b = operands[1].signed_value
            return BoolConstant(a > b, taint=expression.taint)
        return None

    def visit_GreaterOrEqual(self, expression, *operands) -> Optional[BoolConstant]:
        if all(isinstance(o, Constant) for o in operands):
            a = operands[0].signed_value
            b = operands[1].signed_value
            return BoolConstant(a >= b, taint=expression.taint)
        return None

    def visit_BitVecDiv(self, expression, *operands) -> Optional[BitVecConstant]:
        if all(isinstance(o, Constant) for o in operands):
            signmask = operands[0].signmask
            mask = operands[0].mask
            numeral = operands[0].value
            dividend = operands[1].value
            if numeral & signmask:
                numeral = -(mask - numeral - 1)
            if dividend & signmask:
                dividend = -(mask - dividend - 1)
            if dividend == 0:
                result = 0
            else:
                result = math.trunc(Decimal(numeral) / Decimal(dividend))
            return BitVecConstant(expression.size, result, taint=expression.taint)
        return None

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
        if all(isinstance(o, Constant) for o in operands):
            value = operands[0].value
            begining = expression.begining
            end = expression.end
            value = value >> begining
            mask = (1 << (end - begining)) - 1
            value = value & mask
            return BitVecConstant(expression.size, value, taint=expression.taint)

    def visit_BoolAnd(self, expression, a, b):
        if isinstance(a, Constant) and a.value == True:
            return b
        if isinstance(b, Constant) and b.value == True:
            return a

    def _visit_operation(self, expression, *operands):
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

    visit_ArraySelect = _visit_operation
    visit_ArrayOperation = _visit_operation
    visit_BoolOperation = _visit_operation
    visit_BitVecOperation = _visit_operation


@lru_cache(maxsize=128, typed=True)
def constant_folder(expression):
    simp = ConstantFolderSimplifier()
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

    def _visit_operation(self, expression, *operands):
        """ constant folding, if all operands of an expression are a Constant do the math """
        if all(isinstance(o, Constant) for o in operands):
            expression = constant_folder(expression)
        if self._changed(expression, operands):
            expression = self._rebuild(expression, operands)
        return expression

    visit_ArrayOperation = _visit_operation
    visit_BoolOperation = _visit_operation
    visit_BitVecOperation = _visit_operation

    def visit_BitVecZeroExtend(self, expression, *operands):
        if self._changed(expression, operands):
            return BitVecZeroExtend(expression.size, *operands, taint=expression.taint)
        else:
            return expression

    def visit_BoolAnd(self, expression, *operands):
        if isinstance(operands[0], Constant) and operands[0].value:
            return operands[1]
        if isinstance(operands[1], Constant) and operands[1].value:
            return operands[0]

        # AND ( EQ (EXTRACT(0,8, a), EXTRACT(0,8, b)),  EQ (EXTRACT(8,16, a), EXTRACT(8,16 b)) ->
        # EQ(EXTRACT(0,16, a), EXTRACT(0,16, b))
        if isinstance(operands[0], BoolEqual) and isinstance(operands[1], BoolEqual):
            # Eq operands
            operand_0 = operands[0]
            operand_1 = operands[1]
            # Extract operands
            operand_0_0 = operand_0.operands[0]
            operand_0_1 = operand_0.operands[1]
            operand_1_0 = operand_1.operands[0]
            operand_1_1 = operand_1.operands[1]

            if (
                isinstance(operand_0_0, BitVecExtract)
                and isinstance(operand_0_1, BitVecExtract)
                and isinstance(operand_1_0, BitVecExtract)
                and isinstance(operand_1_1, BitVecExtract)
            ):

                if (
                    operand_0_0.value is operand_1_0.value
                    and operand_0_1.value is operand_1_1.value
                    and (operand_0_0.begining, operand_0_0.end)
                    == (operand_0_1.begining, operand_0_1.end)
                    and (operand_1_0.begining, operand_1_0.end)
                    == (operand_1_1.begining, operand_1_1.end)
                ):
                    if ((operand_0_0.end + 1) == operand_1_0.begining) or (
                        operand_0_0.begining == (operand_1_0.end + 1)
                    ):

                        value0 = operand_0_0.value
                        value1 = operand_0_1.value
                        beg = min(operand_0_0.begining, operand_1_0.begining)
                        end = max(operand_0_0.end, operand_1_0.end)
                        return BitVecExtract(value0, beg, end - beg + 1) == BitVecExtract(
                            value1, beg, end - beg + 1
                        )

    def visit_BoolNot(self, expression, *operands):
        if isinstance(operands[0], BoolNot):
            return operands[0].operands[0]

    def visit_BoolEqual(self, expression, *operands):
        """(EQ, ITE(cond, constant1, constant2), constant1) -> cond
        (EQ, ITE(cond, constant1, constant2), constant2) -> NOT cond
        (EQ (extract a, b, c) (extract a, b, c))
        """
        if isinstance(operands[0], BitVecITE) and isinstance(operands[1], Constant):
            if isinstance(operands[0].operands[1], Constant) and isinstance(
                operands[0].operands[2], Constant
            ):
                value1, value2, value3 = (
                    operands[1].value,
                    operands[0].operands[1].value,
                    operands[0].operands[2].value,
                )
                if value1 == value2 and value1 != value3:
                    return operands[0].operands[0]  # FIXME: this may break taint propagation
                elif value1 == value3 and value1 != value2:
                    return BoolNot(operands[0].operands[0], taint=expression.taint)

        if operands[0] is operands[1]:
            return BoolConstant(True, taint=expression.taint)

        if isinstance(operands[0], BitVecExtract) and isinstance(operands[1], BitVecExtract):
            if (
                operands[0].value is operands[1].value
                and operands[0].end == operands[1].end
                and operands[0].begining == operands[1].begining
            ):

                return BoolConstant(True, taint=expression.taint)

    def visit_BoolOr(self, expression, a, b):
        if isinstance(a, Constant):
            if a.value == False:
                return b
            if a.value == True:
                return a
        if isinstance(b, Constant):
            if b.value == False:
                return a
            if b.value == True:
                return b
        if a is b:
            return a

    def visit_BitVecITE(self, expression, *operands):
        if isinstance(operands[0], Constant):
            if operands[0].value:
                result = operands[1]
            else:
                result = operands[2]
            new_taint = result._taint | operands[0].taint
            if result._taint != new_taint:
                result = copy.copy(result)
                result._taint = new_taint
            return result

        if self._changed(expression, operands):
            return BitVecITE(expression.size, *operands, taint=expression.taint)

    def visit_BitVecConcat(self, expression, *operands):
        """concat( extract(k1, 0, a), extract(sizeof(a)-k1, k1, a))  ==> a
        concat( extract(k1, beg, a), extract(end, k1, a))  ==> extract(beg, end, a)
        concat( x , extract(k1, beg, a), extract(end, k1, a), z)  ==> concat( x , extract(k1, beg, a), extract(end, k1, a), z)
        """
        if len(operands) == 1:
            return operands[0]

        changed = False
        last_o = None
        new_operands = []
        for o in operands:
            if isinstance(o, BitVecExtract):
                if last_o is None:
                    last_o = o
                else:
                    if last_o.value is o.value and last_o.begining == o.end + 1:
                        last_o = BitVecExtract(
                            o.value, o.begining, last_o.end - o.begining + 1, taint=expression.taint
                        )
                        changed = True
                    else:
                        new_operands.append(last_o)
                        last_o = o
            else:
                if last_o is not None:
                    new_operands.append(last_o)
                    last_o = None
                new_operands.append(o)
        if last_o is not None:
            new_operands.append(last_o)
        if changed:
            return BitVecConcat(expression.size, *new_operands)

        op = operands[0]
        value = None
        end = None
        begining = None
        for o in operands:
            # If found a non BitVecExtract, do not apply
            if not isinstance(o, BitVecExtract):
                value = None
                break
            # Set the value for the first item
            if value is None:
                value = o.value
                begining = o.begining
                end = o.end
            else:
                # If concat of extracts of different values do not apply
                if value is not o.value:
                    value = None
                    break
                # If concat of non contiguous extracs do not apply
                if begining != o.end + 1:
                    value = None
                    break
                # update begining variable
                begining = o.begining

        if value is not None:
            if end + 1 != value.size or begining != 0:
                return BitVecExtract(value, begining, end - begining + 1, taint=expression.taint)

        return value

    def visit_BitVecExtract(self, expression, *operands):
        """extract(sizeof(a), 0)(a)  ==> a
        extract(16, 0)( concat(a,b,c,d) ) => concat(c, d)
        extract(m,M)(and/or/xor a b ) => and/or/xor((extract(m,M) a) (extract(m,M) a)
        """
        op = operands[0]
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
            for item in reversed(op.operands):
                if size == 0:
                    assert expression.size == sum([x.size for x in new_operands])
                    return BitVecConcat(
                        expression.size, *reversed(new_operands), taint=expression.taint
                    )

                if begining >= item.size:
                    # skip the item
                    begining -= item.size
                else:
                    if begining == 0 and size == item.size:
                        new_operands.append(item)
                        size = 0
                    else:
                        if size <= item.size - begining:
                            new_operands.append(BitVecExtract(item, begining, size))
                            size = 0
                        else:
                            new_operands.append(BitVecExtract(item, begining, item.size - begining))
                            size -= item.size - begining
                            begining = 0
        elif isinstance(op, BitVecConstant):
            return BitVecConstant(size, (op.value >> begining) & ~(1 << size))

        if isinstance(op, (BitVecAnd, BitVecOr, BitVecXor)):
            bitoperand_a, bitoperand_b = op.operands
            return op.__class__(
                BitVecExtract(bitoperand_a, begining, expression.size),
                BitVecExtract(bitoperand_b, begining, expression.size),
                taint=expression.taint,
            )

    def visit_BitVecAdd(self, expression, *operands):
        """a + 0  ==> a
        0 + a  ==> a
        """
        left = operands[0]
        right = operands[1]
        if isinstance(right, BitVecConstant):
            if right.value == 0:
                return left
        if isinstance(left, BitVecConstant):
            if left.value == 0:
                return right

    def visit_BitVecSub(self, expression, *operands):
        """a - 0 ==> 0
        (a + b) - b  ==> a
        (b + a) - b  ==> a
        """
        left = operands[0]
        right = operands[1]
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
        """a | 0 => a
        0 | a => a
        0xffffffff & a => 0xffffffff
        a & 0xffffffff => 0xffffffff

        """
        left = operands[0]
        right = operands[1]
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
        """ct & x => x & ct                move constants to the right
        a & 0 => 0                      remove zero
        a & 0xffffffff => a             remove full mask
        (b & ct2) & ct => b & (ct&ct2)  associative property
        (a & (b | c) => a&b | a&c       distribute over |
        """
        left = operands[0]
        right = operands[1]
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
        """a << 0 => a                       remove zero
        a << ct => 0 if ct > sizeof(a)    remove big constant shift
        """
        left = operands[0]
        right = operands[1]
        if isinstance(right, BitVecConstant):
            if right.value == 0:
                return left
            elif right.value >= right.size:
                return left

    def visit_ArraySelect(self, expression, *operands):
        """ArraySelect (ArrayStore((ArrayStore(x0,v0) ...),xn, vn), x0)
        -> v0
        """
        arr, index = operands
        if isinstance(arr, ArrayVariable):
            return self._visit_operation(expression, *operands)

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
            if arr.value is not None:
                return arr.value
        else:
            if arr is not expression.array:
                out = arr.select(index)
                if out is not None:
                    return arr.select(index)
        return self._visit_operation(expression, *operands)

    def visit_Expression(self, expression, *operands):
        assert len(operands) == 0
        assert not isinstance(expression, Operation)
        return expression


@lru_cache(maxsize=128, typed=True)
def arithmetic_simplify(expression):
    simp = ArithmeticSimplifier()
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


@lru_cache(maxsize=128, typed=True)
def simplify(expression):
    expression = arithmetic_simplify(expression)
    return expression


class TranslatorSmtlib(Translator):
    """Simple visitor to translate an expression to its smtlib representation"""

    unique = 0
    unique_lock = threading.Lock()

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

        with TranslatorSmtlib.unique_lock:
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
        BoolEqual: "=",
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

    def _visit_variable(self, expression):
        return expression.name

    visit_ArrayVariable = _visit_variable
    visit_BitVecVariable = _visit_variable
    visit_BoolVariable = _visit_variable

    def visit_ArraySelect(self, expression, *operands):
        array_smt, index_smt = operands
        if isinstance(expression.array, ArrayStore):
            array_smt = self._add_binding(expression.array, array_smt)

        return "(select %s %s)" % (array_smt, index_smt)

    def _visit_operation(self, expression, *operands):
        operation = self.translation_table[type(expression)]
        if isinstance(expression, (BitVecSignExtend, BitVecZeroExtend)):
            operation = operation % expression.extend
        elif isinstance(expression, BitVecExtract):
            operation = operation % (expression.end, expression.begining)

        operands = [self._add_binding(*x) for x in zip(expression.operands, operands)]
        return "(%s %s)" % (operation, " ".join(operands))

    visit_ArrayOperation = _visit_operation
    visit_BoolOperation = _visit_operation
    visit_BitVecOperation = _visit_operation

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

    def _visit_variable(self, expression):
        if expression in self._replace_bindings:
            return self._replace_bindings[expression]
        return expression

    visit_ArrayVariable = _visit_variable
    visit_BitVecVariable = _visit_variable
    visit_BoolVariable = _visit_variable


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
    if isinstance(expression, ArrayProxy):
        expression = expression.array

    visitor = GetDeclarations()
    visitor.visit(expression)
    return visitor.result
