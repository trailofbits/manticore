"""Symbolic EVM implementation based on the yellow paper: http://gavwood.com/paper.pdf"""
import binascii
import random
import io
import copy
import inspect
from functools import wraps
from typing import List, Set, Tuple, Union
from ..utils.helpers import issymbolic, get_taints, taint_with, istainted
from ..platforms.platform import *
from ..core.smtlib import (
    Z3Solver,
    BitVec,
    Array,
    ArrayProxy,
    Operators,
    Constant,
    ArrayVariable,
    ArrayStore,
    BitVecConstant,
    translate_to_smtlib,
    to_constant,
    simplify,
)
from ..core.state import Concretize, TerminateState
from ..utils.event import Eventful
from ..utils import config
from ..core.smtlib.visitors import simplify
from ..exceptions import EthereumError
import pyevmasm as EVMAsm
import logging
from collections import namedtuple
import sha3
import rlp
import time

logger = logging.getLogger(__name__)

# Gas behaviour configuration
# When gas is concrete the gas checks and calculation are pretty straigth forward
# Though Gas can became symbolic in normal bytecode execution for example at instructions
# MSTORE, MSTORE8, EXP, ... and every instruction with internal operation restricted by gas
# This configuration variable allows the user to control and perhaps relax the gas calculation
# This configuration variable allows the user to control and perhaps relax the gas calculation
# pedantic: gas is faithfully accounted and checked at instruction level. State may get forked in OOG/NoOOG
# complete: gas is faithfully accounted and checked at basic blocks limits. State may get forked in OOG/NoOOG
# concrete: concretize gas: if the fee to be consumed gets to be symbolic choose some potential values and fork on those
# optimistic: Try not to OOG. If it may be enough gas we ignore the OOG case. A constraint is added to assert the gas is enough and the OOG state is ignored.
# pesimistic: OOG soon. If it may NOT be enough gas we ignore the normal case. A constraint is added to assert the gas is NOT enough and the other state is ignored.
# ignore: Ignore gas. Do not account for it. Do not OOG.
consts = config.get_group("evm")

consts.add(
    "oog",
    default="pedantic",
    description=(
        "Default behavior for symbolic gas."
        "pedantic: Fully faithful. Test at every instruction. Forks."
        "complete: Mostly faithful. Test at BB limit. Forks."
        "concrete: Incomplete. Concretize gas to MIN/MAX values. Forks."
        "optimistic: Try to not fail due to OOG. If it can be enough gas use it. Ignore the path to OOG. Wont fork"
        "pesimistic: Try OOG asap. Fail soon. Ignore the path with enough gas."
        "ignore: Ignore gas. Instructions won't consume gas"
    ),
)

# Auxiliary constants and functions
TT256 = 2 ** 256
TT256M1 = 2 ** 256 - 1
MASK160 = 2 ** 160 - 1
TT255 = 2 ** 255
TOOHIGHMEM = 0x1000
DEFAULT_FORK = "byzantium"

# FIXME. We should just use a Transaction() for this
PendingTransaction = namedtuple(
    "PendingTransaction", ["type", "address", "price", "data", "caller", "value", "gas"]
)
EVMLog = namedtuple("EVMLog", ["address", "memlog", "topics"])


def ceil32(x):
    size = 256
    if isinstance(x, BitVec):
        size = x.size
    return Operators.ITEBV(size, Operators.UREM(x, 32) == 0, x, x + 32 - Operators.UREM(x, 32))


def to_signed(i):
    return Operators.ITEBV(256, i < TT255, i, i - TT256)


class Transaction:
    __slots__ = (
        "_sort",
        "address",
        "price",
        "data",
        "caller",
        "value",
        "depth",
        "_return_data",
        "_result",
        "gas",
    )

    def __init__(
        self,
        sort,
        address,
        price,
        data,
        caller,
        value,
        gas=0,
        depth=None,
        result=None,
        return_data=None,
    ):
        self.sort = sort
        self.address = address
        self.price = price
        self.data = data
        self.caller = caller
        self.value = value
        self.depth = depth
        self.gas = gas
        self.set_result(result, return_data)

    def concretize(self, state):
        conc_caller = state.solve_one(self.caller)
        conc_address = state.solve_one(self.address)
        conc_value = state.solve_one(self.value)
        conc_gas = state.solve_one(self.gas)
        conc_data = state.solve_one(self.data)
        conc_return_data = state.solve_one(self.return_data)

        return Transaction(
            self.sort,
            conc_address,
            self.price,
            conc_data,
            conc_caller,
            conc_value,
            conc_gas,
            depth=self.depth,
            result=self.result,
            return_data=bytearray(conc_return_data),
        )

    def to_dict(self, mevm):
        """
        Only meant to be used with concrete Transaction objects! (after calling .concretize())
        """
        return dict(
            type=self.sort,
            from_address=self.caller,
            from_name=mevm.account_name(self.caller),
            to_address=self.address,
            to_name=mevm.account_name(self.address),
            value=self.value,
            gas=self.gas,
            data=binascii.hexlify(self.data).decode(),
        )

    def dump(self, stream, state, mevm, conc_tx=None):
        """
        Concretize and write a human readable version of the transaction into the stream. Used during testcase
        generation.

        :param stream: Output stream to write to. Typically a file.
        :param manticore.ethereum.State state: state that the tx exists in
        :param manticore.ethereum.ManticoreEVM mevm: manticore instance
        :return:
        """
        from ..ethereum import ABI  # circular imports
        from ..ethereum.manticore import flagged

        is_something_symbolic = False

        if conc_tx is None:
            conc_tx = self.concretize(state)

        # The result if any RETURN or REVERT
        stream.write("Type: %s (%d)\n" % (self.sort, self.depth))

        caller_solution = conc_tx.caller

        caller_name = mevm.account_name(caller_solution)
        stream.write(
            "From: %s(0x%x) %s\n" % (caller_name, caller_solution, flagged(issymbolic(self.caller)))
        )

        address_solution = conc_tx.address
        address_name = mevm.account_name(address_solution)

        stream.write(
            "To: %s(0x%x) %s\n"
            % (address_name, address_solution, flagged(issymbolic(self.address)))
        )
        stream.write("Value: %d %s\n" % (conc_tx.value, flagged(issymbolic(self.value))))
        stream.write("Gas used: %d %s\n" % (conc_tx.gas, flagged(issymbolic(self.gas))))

        tx_data = conc_tx.data

        stream.write(
            "Data: 0x{} {}\n".format(
                binascii.hexlify(tx_data).decode(), flagged(issymbolic(self.data))
            )
        )

        if self.return_data is not None:
            return_data = conc_tx.return_data

            stream.write(
                "Return_data: 0x{} {}\n".format(
                    binascii.hexlify(return_data).decode(), flagged(issymbolic(self.return_data))
                )
            )

        metadata = mevm.get_metadata(self.address)
        if self.sort == "CREATE":
            if metadata is not None:

                conc_args_data = conc_tx.data[len(metadata._init_bytecode) :]
                arguments = ABI.deserialize(metadata.get_constructor_arguments(), conc_args_data)

                # TODO confirm: arguments should all be concrete?

                is_argument_symbolic = any(
                    map(issymbolic, arguments)
                )  # is this redundant since arguments are all concrete?
                stream.write("Function call:\n")
                stream.write("Constructor(")
                stream.write(
                    ",".join(map(repr, map(state.solve_one, arguments)))
                )  # is this redundant since arguments are all concrete?
                stream.write(") -> %s %s\n" % (self.result, flagged(is_argument_symbolic)))

        if self.sort == "CALL":
            if metadata is not None:
                calldata = conc_tx.data
                is_calldata_symbolic = issymbolic(self.data)

                function_id = calldata[:4]  # hope there is enough data
                signature = metadata.get_func_signature(function_id)
                function_name = metadata.get_func_name(function_id)
                if signature:
                    _, arguments = ABI.deserialize(signature, calldata)
                else:
                    arguments = (calldata,)

                return_data = None
                if self.result == "RETURN":
                    ret_types = metadata.get_func_return_types(function_id)
                    return_data = conc_tx.return_data
                    return_values = ABI.deserialize(ret_types, return_data)  # function return

                is_return_symbolic = issymbolic(self.return_data)

                stream.write("\n")
                stream.write("Function call:\n")
                stream.write("%s(" % function_name)
                stream.write(",".join(map(repr, arguments)))
                stream.write(") -> %s %s\n" % (self.result, flagged(is_calldata_symbolic)))

                if return_data is not None:
                    if len(return_values) == 1:
                        return_values = return_values[0]

                    stream.write("return: %r %s\n" % (return_values, flagged(is_return_symbolic)))
                is_something_symbolic = is_calldata_symbolic or is_return_symbolic

        stream.write("\n\n")
        return is_something_symbolic

    @property
    def sort(self):
        return self._sort

    @sort.setter
    def sort(self, sort):
        if sort not in {"CREATE", "CALL", "DELEGATECALL"}:
            raise EVMException("Invalid transaction type")
        self._sort = sort

    @property
    def result(self):
        return self._result

    @property
    def is_human(self):
        """
        Returns whether this is a transaction made by human (in a script).

        As an example for:
            contract A { function a(B b) { b.b(); } }
            contract B { function b() {} }

        Calling `B.b()` makes a human transaction.
        Calling `A.a(B)` makes a human transaction which makes an internal transaction (b.b()).
        """
        return self.depth == 0

    @property
    def return_data(self):
        return self._return_data

    @property
    def return_value(self):
        if self.result in {"RETURN", "STOP", "SELFDESTRUCT"}:
            return 1
        else:
            assert self.result in {"TXERROR", "REVERT", "THROW"}
            return 0

    def set_result(self, result, return_data=None):
        if getattr(self, "result", None) is not None:
            raise EVMException("Transaction result already set")
        if result not in {None, "TXERROR", "REVERT", "RETURN", "THROW", "STOP", "SELFDESTRUCT"}:
            raise EVMException("Invalid transaction result")
        if result in {"RETURN", "REVERT"}:
            if not isinstance(return_data, (bytes, bytearray, Array)):
                raise EVMException(
                    "Invalid transaction return_data type:", type(return_data).__name__
                )
        elif result in {"STOP", "THROW", "SELFDESTRUCT"}:
            if return_data is None:
                return_data = bytearray()
            if not isinstance(return_data, (bytes, bytearray, Array)) or len(return_data) != 0:
                raise EVMException(
                    f"Invalid transaction return_data. Too much data ({len(return_data)}) for STOP, THROW or SELFDESTRUCT"
                )
        else:
            if return_data is not None:
                raise EVMException("Invalid transaction return_data")
        self._result = result
        self._return_data = return_data

    def __reduce__(self):
        """Implements serialization/pickle"""
        return (
            self.__class__,
            (
                self.sort,
                self.address,
                self.price,
                self.data,
                self.caller,
                self.value,
                self.gas,
                self.depth,
                self.result,
                self.return_data,
            ),
        )

    def __str__(self):
        return "Transaction({:s}, from=0x{:x}, to=0x{:x}, value={!r}, depth={:d}, data={!r}, result={!r}..)".format(
            self.sort, self.caller, self.address, self.value, self.depth, self.data, self.result
        )


# Exceptions...
class EVMException(Exception):
    pass


class ConcretizeArgument(EVMException):
    """
    Raised when a symbolic argument needs to be concretized.
    """

    def __init__(self, pos, expression=None, policy="SAMPLED"):
        self.message = "Concretizing evm stack item {}".format(pos)
        self.pos = pos
        self.expression = expression
        self.policy = policy


class ConcretizeFee(EVMException):
    """
    Raised when a symbolic gas fee needs to be concretized.
    """

    def __init__(self, policy="MINMAX"):
        self.message = "Concretizing evm instruction gas fee"
        self.policy = policy


class ConcretizeGas(EVMException):

    """
    Raised when a symbolic gas needs to be concretized.
    """

    def __init__(self, policy="MINMAX"):
        self.message = "Concretizing evm gas"
        self.policy = policy


class StartTx(EVMException):
    """A new transaction is started"""

    pass


class EndTx(EVMException):
    """The current transaction ends"""

    def __init__(self, result, data=None):
        if result not in {None, "TXERROR", "REVERT", "RETURN", "THROW", "STOP", "SELFDESTRUCT"}:
            raise EVMException("Invalid end transaction result")
        if result is None and data is not None:
            raise EVMException("Invalid end transaction result")
        if not isinstance(data, (type(None), Array, bytes)):
            raise EVMException("Invalid end transaction data type")
        self.result = result
        self.data = data

    def is_rollback(self):
        if self.result in {"STOP", "RETURN", "SELFDESTRUCT"}:
            return False
        else:
            assert self.result in {"THROW", "TXERROR", "REVERT"}
            return True

    def __str__(self):
        return f"EndTX<{self.result}>"


class InvalidOpcode(EndTx):
    """Trying to execute invalid opcode"""

    def __init__(self):
        super().__init__("THROW")


class StackOverflow(EndTx):
    """Attempted to push more than 1024 items"""

    def __init__(self):
        super().__init__("THROW")


class StackUnderflow(EndTx):
    """Attempted to pop from an empty stack"""

    def __init__(self):
        super().__init__("THROW")


class NotEnoughGas(EndTx):
    """Not enough gas for operation"""

    def __init__(self):
        super().__init__("THROW")


class Stop(EndTx):
    """Program reached a STOP instruction"""

    def __init__(self):
        super().__init__("STOP")


class Return(EndTx):
    """Program reached a RETURN instruction"""

    def __init__(self, data=bytearray()):
        super().__init__("RETURN", data)


class Revert(EndTx):
    """Program reached a REVERT instruction"""

    def __init__(self, data):
        super().__init__("REVERT", data)


class SelfDestruct(EndTx):
    """Program reached a SELFDESTRUCT instruction"""

    def __init__(self):
        super().__init__("SELFDESTRUCT")


class TXError(EndTx):
    """A failed Transaction"""

    def __init__(self):
        super().__init__("TXERROR")


def concretized_args(**policies):
    """
    Make sure an EVM instruction has all of its arguments concretized according to
    provided policies.

    Example decoration:

        @concretized_args(size='ONE', address='')
        def LOG(self, address, size, *topics):
            ...

    The above will make sure that the |size| parameter to LOG is Concretized when symbolic
    according to the 'ONE' policy and concretize |address| with the default policy.

    :param policies: A kwargs list of argument names and their respective policies.
                         Provide None or '' as policy to use default.
    :return: A function decorator
    """

    def concretizer(func):
        spec = inspect.getfullargspec(func)

        @wraps(func)
        def wrapper(*args, **kwargs):
            for arg, policy in policies.items():
                assert arg in spec.args, "Concretizer argument not found in wrapped function."
                # index is 0-indexed, but ConcretizeArgument is 1-indexed. However, this is correct
                # since implementation method is always a bound method (self is param 0)
                index = spec.args.index(arg)
                if not issymbolic(args[index]):
                    continue
                if not policy:
                    policy = "SAMPLED"

                if policy == "ACCOUNTS":
                    value = args[index]
                    world = args[0].world
                    # special handler for EVM only policy
                    cond = world._constraint_to_accounts(value, ty="both", include_zero=True)
                    world.constraints.add(cond)
                    policy = "ALL"

                if args[index].taint:
                    # TODO / FIXME: The taint should persist!
                    logger.warning(
                        f"Concretizing {func.__name__}'s {index} argument and dropping its taints: "
                        "the value might not be tracked properly (in case of using detectors)"
                    )
                logger.info(f"Concretizing instruction argument {arg} by {policy}")
                raise ConcretizeArgument(index, policy=policy)
            return func(*args, **kwargs)

        wrapper.__signature__ = inspect.signature(func)
        return wrapper

    return concretizer


class EVM(Eventful):
    """
    Machine State. The machine state is defined as
    the tuple (g, pc, m, i, s) which are the gas available, the
    program counter pc , the memory contents, the active
    number of words in memory (counting continuously
    from position 0), and the stack contents. The memory
    contents are a series of zeroes of bitsize 256
    """

    _published_events = {
        "evm_execute_instruction",
        "evm_read_storage",
        "evm_write_storage",
        "evm_read_memory",
        "evm_write_memory",
        "evm_read_code",
        "decode_instruction",
        "concrete_sha3",
        "symbolic_sha3",
    }

    class transact:
        def __init__(self, pre=None, pos=None, doc=None):
            self._pre = pre
            self._pos = pos
            if doc is None and pre is not None:
                doc = pre.__doc__
            self.__doc__ = doc
            self.__name__ = pre.__name__

        def __get__(self, obj, objtype=None):
            if obj is None:
                return self
            if self._pre is None:
                raise AttributeError("unreadable attribute")
            from types import MethodType

            # return different version depending on obj._pending_transaction
            def _pre_func(my_obj, *args, **kwargs):
                if my_obj._on_transaction:
                    result = self._pos(my_obj, *args, **kwargs)
                    my_obj._on_transaction = False
                    return result
                else:
                    try:
                        self._pre(my_obj, *args, **kwargs)
                        raise AssertionError(
                            "The pre-transaction handler must raise a StartTx transaction"
                        )
                    except StartTx:
                        my_obj._on_transaction = True
                        raise

            return MethodType(_pre_func, obj)

        def __set__(self, obj, value):
            raise AttributeError("can't set attribute")

        def __delete__(self, obj):
            raise AttributeError("can't delete attribute")

        def pos(self, pos):
            return type(self)(self._pre, pos)

    def __init__(
        self, constraints, address, data, caller, value, bytecode, world=None, gas=210000, **kwargs
    ):
        """
        Builds a Ethereum Virtual Machine instance

        :param memory: the initial memory
        :param address: the address of the account which owns the code that is executing.
        :param data: the byte array that is the input data to this execution
        :param caller: the address of the account which caused the code to be executing. A 160-bit code used for identifying Accounts
        :param value: the value, in Wei, passed to this account as part of the same procedure as execution. One Ether is defined as being 10**18 Wei
        :param bytecode: the byte array that is the machine code to be executed
        :param world: the EVMWorld object where the transaction is being executed
        :param gas: gas budget for this transaction
        """
        super().__init__(**kwargs)
        if data is not None and not issymbolic(data):
            data_size = len(data)
            data_symbolic = constraints.new_array(
                index_bits=256,
                value_bits=8,
                index_max=data_size,
                name=f"DATA_{address:x}",
                avoid_collisions=True,
                default=0,
            )
            data_symbolic[0:data_size] = data
            data = data_symbolic

        if bytecode is not None and not issymbolic(bytecode):
            bytecode_size = len(bytecode)
            bytecode_symbolic = constraints.new_array(
                index_bits=256,
                value_bits=8,
                index_max=bytecode_size,
                name=f"BYTECODE_{address:x}",
                avoid_collisions=True,
                default=0,
            )
            bytecode_symbolic[0:bytecode_size] = bytecode
            bytecode = bytecode_symbolic

        # TODO: Handle the case in which bytecode is symbolic (This happens at
        # CREATE instructions that has the arguments appended to the bytecode)
        # This is a very cornered corner case in which code is actually symbolic
        # We should simply not allow to jump to unconstrained(*) symbolic code.
        # (*) bytecode that could take more than a single value
        self._check_jumpdest = False
        self._valid_jumpdests = set()

        # Compile the list of valid jumpdests via linear dissassembly
        def extend_with_zeroes(b):
            try:
                for x in b:
                    x = to_constant(x)
                    if isinstance(x, int):
                        yield (x)
                    else:
                        yield (0)
                for _ in range(32):
                    yield (0)
            except Exception as e:
                return

        for i in EVMAsm.disassemble_all(extend_with_zeroes(bytecode)):
            if i.mnemonic == "JUMPDEST":
                self._valid_jumpdests.add(i.pc)

        # A no code VM is used to execute transactions to normal accounts.
        # I'll execute a STOP and close the transaction
        # if len(bytecode) == 0:
        #    raise EVMException("Need code")
        self._constraints = constraints
        # Uninitialized values in memory are 0 by spec
        self.memory = constraints.new_array(
            index_bits=256,
            value_bits=8,
            name=f"EMPTY_MEMORY_{address:x}",
            avoid_collisions=True,
            default=0,
        )
        self.address = address
        self.caller = (
            caller
        )  # address of the account that is directly responsible for this execution
        self.data = data
        self.value = value
        self._bytecode = bytecode
        self.suicides = set()
        self.logs = []
        # FIXME parse decode and mark invalid instructions
        # self.invalid = set()

        # Machine state
        self.pc = 0
        self.stack = []
        # We maintain gas as a 512 bits internally to avoid overflows
        # it is shortened to 256 bits when it is used by the GAS instruction
        self._gas = Operators.ZEXTEND(gas, 512)
        self._world = world
        self._allocated = 0
        self._on_transaction = False  # for @transact
        self._checkpoint_data = None
        self._published_pre_instruction_events = False

        # Used calldata size
        min_size = 0
        max_size = len(self.data)
        self._used_calldata_size = 0
        self._calldata_size = len(self.data)
        self._valid_jmpdests = set()

    @property
    def bytecode(self):
        return self._bytecode

    @property
    def constraints(self):
        return self._constraints

    @constraints.setter
    def constraints(self, constraints):
        self._constraints = constraints
        self.memory.constraints = constraints

    @property
    def gas(self):
        return self._gas

    def __getstate__(self):
        state = super().__getstate__()
        state["memory"] = self.memory
        state["world"] = self._world
        state["constraints"] = self.constraints
        state["address"] = self.address
        state["caller"] = self.caller
        state["data"] = self.data
        state["value"] = self.value
        state["bytecode"] = self._bytecode
        state["pc"] = self.pc
        state["stack"] = self.stack
        state["gas"] = self._gas
        state["allocated"] = self._allocated
        state["suicides"] = self.suicides
        state["logs"] = self.logs
        state["_on_transaction"] = self._on_transaction
        state["_checkpoint_data"] = self._checkpoint_data
        state["_published_pre_instruction_events"] = self._published_pre_instruction_events
        state["_used_calldata_size"] = self._used_calldata_size
        state["_calldata_size"] = self._calldata_size
        state["_valid_jumpdests"] = self._valid_jumpdests
        state["_check_jumpdest"] = self._check_jumpdest
        return state

    def __setstate__(self, state):
        self._checkpoint_data = state["_checkpoint_data"]
        self._published_pre_instruction_events = state["_published_pre_instruction_events"]
        self._on_transaction = state["_on_transaction"]
        self._gas = state["gas"]
        self.memory = state["memory"]
        self.logs = state["logs"]
        self._world = state["world"]
        self.constraints = state["constraints"]
        self.address = state["address"]
        self.caller = state["caller"]
        self.data = state["data"]
        self.value = state["value"]
        self._bytecode = state["bytecode"]
        self.pc = state["pc"]
        self.stack = state["stack"]
        self._allocated = state["allocated"]
        self.suicides = state["suicides"]
        self._used_calldata_size = state["_used_calldata_size"]
        self._calldata_size = state["_calldata_size"]
        self._valid_jumpdests = state["_valid_jumpdests"]
        self._check_jumpdest = state["_check_jumpdest"]
        super().__setstate__(state)

    def _get_memfee(self, address, size=1):
        """
        This calculates the amount of extra gas needed for accessing to
        previously unused memory.

        :param address: base memory offset
        :param size: size of the memory access
        """
        if not issymbolic(size) and size == 0:
            return 0

        address = self.safe_add(address, size)
        allocated = self.allocated
        GMEMORY = 3
        GQUADRATICMEMDENOM = 512  # 1 gas per 512 quadwords
        old_size = Operators.ZEXTEND(Operators.UDIV(self.safe_add(allocated, 31), 32), 512)
        new_size = Operators.ZEXTEND(Operators.UDIV(self.safe_add(address, 31), 32), 512)

        old_totalfee = self.safe_mul(old_size, GMEMORY) + Operators.UDIV(
            self.safe_mul(old_size, old_size), GQUADRATICMEMDENOM
        )
        new_totalfee = self.safe_mul(new_size, GMEMORY) + Operators.UDIV(
            self.safe_mul(new_size, new_size), GQUADRATICMEMDENOM
        )
        memfee = new_totalfee - old_totalfee
        flag = Operators.UGT(new_totalfee, old_totalfee)
        return Operators.ITEBV(512, size == 0, 0, Operators.ITEBV(512, flag, memfee, 0))

    def _allocate(self, address, size=1):
        address_c = Operators.UDIV(Operators.ZEXTEND(address, 512) + size + 31, 32) * 32
        self._allocated = Operators.ITEBV(
            512, Operators.UGT(address_c, self._allocated), address_c, self.allocated
        )

    @property
    def allocated(self):
        return self._allocated

    @property
    def world(self):
        return self._world

    @staticmethod
    def check256int(value):
        assert True

    def read_code(self, address, size=1):
        """
        Read size byte from bytecode.
        If less than size bytes are available result will be pad with \x00
        """
        assert address < len(self.bytecode)
        value = self.bytecode[address : address + size]
        if len(value) < size:
            value += "\x00" * (size - len(value))  # pad with null (spec)
        return value

    def disassemble(self):
        return EVMAsm.disassemble(self.bytecode)

    @property
    def PC(self):
        return self.pc

    @property
    def instruction(self):
        """
        Current instruction pointed by self.pc
        """
        # FIXME check if pc points to invalid instruction
        # if self.pc >= len(self.bytecode):
        #    return InvalidOpcode('Code out of range')
        # if self.pc in self.invalid:
        #    raise InvalidOpcode('Opcode inside a PUSH immediate')
        try:
            _decoding_cache = getattr(self, "_decoding_cache")
        except Exception:
            _decoding_cache = self._decoding_cache = {}

        pc = self.pc
        if isinstance(pc, Constant):
            pc = pc.value

        if pc in _decoding_cache:
            return _decoding_cache[pc]

        def getcode():
            bytecode = self.bytecode
            for pc_i in range(pc, len(bytecode)):
                yield simplify(bytecode[pc_i]).value
            while True:
                yield 0

        instruction = EVMAsm.disassemble_one(getcode(), pc=pc, fork=DEFAULT_FORK)
        _decoding_cache[pc] = instruction
        return instruction

    # auxiliary funcs
    # Stack related
    def _push(self, value):
        """
        Push into the stack

              ITEM0
              ITEM1
              ITEM2
        sp->  {empty}
        """
        assert isinstance(value, int) or isinstance(value, BitVec) and value.size == 256
        if len(self.stack) >= 1024:
            raise StackOverflow()

        if isinstance(value, int):
            value = value & TT256M1

        value = simplify(value)
        if isinstance(value, Constant) and not value.taint:
            value = value.value
        self.stack.append(value)

    def _top(self, n=0):
        """Read a value from the top of the stack without removing it"""
        if len(self.stack) - n < 0:
            raise StackUnderflow()
        return self.stack[n - 1]

    def _pop(self):
        """Pop a value from the stack"""
        if not self.stack:
            raise StackUnderflow()
        return self.stack.pop()

    def _consume(self, fee):
        # Check type and bitvec size
        if isinstance(fee, int):
            if fee > (1 << 512) - 1:
                raise ValueError
        elif isinstance(fee, BitVec):
            if fee.size != 512:
                raise ValueError("Fees should be 512 bit long")
        # This configuration variable allows the user to control and perhaps relax the gas calculation
        # pedantic: gas is faithfully accounted and checked at instruction level. State may get forked in OOG/NoOOG
        # complete: gas is faithfully accounted and checked at basic blocks limits. State may get forked in OOG/NoOOG
        # concrete: Concretize gas. If the fee to be consumed gets to be symbolic. Choose some potential values and fork on those.
        # optimistic: Try not to OOG. If it may be enough gas we ignore the OOG case. A constraint is added to assert the gas is enough and the OOG state is ignored.
        # pesimistic: OOG soon. If it may NOT be enough gas we ignore the normal case. A constraint is added to assert the gas is NOT enough and the other state is ignored.
        # ignore: Ignore gas. Do not account for it. Do not OOG.

        # optimization that speed up concrete fees sometimes
        if not issymbolic(fee) and issymbolic(self._gas):
            reps, m = getattr(self, "_mgas", (0, None))
            reps += 1
            if m is None and reps > 10:
                m = Z3Solver.instance().min(self.constraints, self._gas)
            self._mgas = reps, m

            if m is not None and fee < m:
                self._gas -= fee
                self._mgas = reps, m - fee
                return

        if consts.oog in ("pedantic", "complete"):
            # gas is faithfully accounted and ogg checked at instruction/BB level.
            if consts.oog == "pedantic" or self.instruction.is_terminator:
                # explore both options / fork

                # FIXME if gas can be both enough and insufficient this will
                #  reenter here and generate redundant queries
                if not issymbolic(self._gas) and not issymbolic(fee):
                    enough_gas_solutions = (self._gas - fee >= 0,)
                else:
                    constraint = simplify(Operators.UGT(self._gas, fee))
                    enough_gas_solutions = Z3Solver.instance().get_all_values(
                        self.constraints, constraint
                    )

                if len(enough_gas_solutions) == 2:
                    # if gas can be both enough and insufficient, fork
                    raise Concretize(
                        "Concretize gas fee",
                        expression=Operators.UGT(self._gas, fee),
                        setstate=None,
                        policy="ALL",
                    )
                elif enough_gas_solutions[0] is False:
                    # if gas if only insuficient OOG!
                    logger.debug(
                        f"Not enough gas for instruction {self.instruction.name} at 0x{self.pc:x}"
                    )
                    raise NotEnoughGas()
                else:
                    assert enough_gas_solutions[0] is True
                    # if there is enough gas keep going
        elif consts.oog == "concrete":
            # Keep gas concrete. Concretize symbolic fees to some values.
            # this can happen only if symbolic gas is provided for the TX
            if issymbolic(self._gas):
                raise ConcretizeGas()
            if issymbolic(fee):
                raise ConcretizeFee()
        elif consts.oog == "optimistic":
            # Try not to OOG. If it may be enough gas we ignore the OOG case.
            # A constraint is added to assert the gas is enough and the OOG state is ignored.
            # explore only when there is enough gas if possible
            if Z3Solver.instance().can_be_true(self.constraints, Operators.UGT(self.gas, fee)):
                self.constraints.add(Operators.UGT(self.gas, fee))
            else:
                logger.debug(
                    f"Not enough gas for instruction {self.instruction.name} at 0x{self.pc:x}"
                )
                raise NotEnoughGas()
        elif consts.oog == "pesimistic":
            # OOG soon. If it may NOT be enough gas we ignore the normal case.
            # A constraint is added to assert the gas is NOT enough and the other state is ignored.
            # explore only when there is enough gas if possible
            if Z3Solver.instance().can_be_true(self.constraints, Operators.ULE(self.gas, fee)):
                self.constraints.add(Operators.ULE(self.gas, fee))
                raise NotEnoughGas()
        else:
            if consts.oog != "ignore":
                raise Exception("Wrong oog config variable")
            # do nothing. gas is not even changed
            return
        self._gas = simplify(self._gas - fee)

        # If everything is concrete lets just check at every instruction
        if not issymbolic(self._gas) and self._gas < 0:
            raise NotEnoughGas()

    def _indemnify(self, fee):
        self._gas += fee

    def _pop_arguments(self):
        # Get arguments (imm, pop)
        current = self.instruction
        arguments = []
        if current.has_operand:
            arguments.append(current.operand)
        for _ in range(current.pops):
            arguments.append(self._pop())
        # simplify stack arguments
        for i, arg in enumerate(arguments):
            if isinstance(arg, Constant) and not arg.taint:
                arguments[i] = arg.value
        return arguments

    def _top_arguments(self):
        # Get arguments (imm, top). Stack is not changed
        current = self.instruction
        arguments = []
        if current.has_operand:
            arguments.append(current.operand)

        if current.pops:
            arguments.extend(reversed(self.stack[-current.pops :]))
        return arguments

    def _push_arguments(self, arguments):
        # Immediate operands should not be pushed
        start = int(self.instruction.has_operand)
        for arg in reversed(arguments[start:]):
            self._push(arg)

    def _push_results(self, instruction, result):
        # Check result (push)
        if instruction.pushes > 1:
            assert len(result) == instruction.pushes
            for value in reversed(result):
                self._push(value)
        elif instruction.pushes == 1:
            self._push(result)
        else:
            assert instruction.pushes == 0
            assert result is None

    def _calculate_gas(self, *arguments):
        current = self.instruction
        implementation = getattr(self, f"{current.semantics}_gas", None)
        if implementation is None:
            return current.fee
        return current.fee + implementation(*arguments)

    def _handler(self, *arguments):
        current = self.instruction
        implementation = getattr(self, current.semantics, None)
        if implementation is None:
            raise TerminateState(f"Instruction not implemented {current.semantics}", testcase=True)
        return implementation(*arguments)

    def _checkpoint(self):
        """Save and/or get a state checkpoint previous to current instruction"""
        # Fixme[felipe] add a with self.disabled_events context manager to Eventful
        if self._checkpoint_data is None:
            if not self._published_pre_instruction_events:
                self._published_pre_instruction_events = True
                self._publish("will_decode_instruction", self.pc)
                self._publish(
                    "will_evm_execute_instruction", self.instruction, self._top_arguments()
                )

            pc = self.pc
            instruction = self.instruction
            old_gas = self.gas
            allocated = self._allocated
            # FIXME Not clear which exception should trigger first. OOG or insufficient stack
            # this could raise an insufficient stack exception
            arguments = self._pop_arguments()
            fee = self._calculate_gas(*arguments)

            self._checkpoint_data = (pc, old_gas, instruction, arguments, fee, allocated)
            self._consume(fee)

        return self._checkpoint_data

    def _rollback(self):
        """Revert the stack, gas, pc and memory allocation so it looks like before executing the instruction"""
        last_pc, last_gas, last_instruction, last_arguments, fee, allocated = self._checkpoint_data
        self._push_arguments(last_arguments)
        self._gas = last_gas
        self._pc = last_pc
        self._allocated = allocated
        self._checkpoint_data = None

    def _set_check_jmpdest(self, flag=True):
        """
        Next instruction must be a JUMPDEST iff `flag` holds.

        Note that at this point `flag` can be the conditional from a JUMPI
        instruction hence potentially a symbolic value.
        """
        self._check_jumpdest = flag

    def _check_jmpdest(self):
        """
        If the previous instruction was a JUMP/JUMPI and the conditional was
        True, this checks that the current instruction must be a JUMPDEST.

        Here, if symbolic, the conditional `self._check_jumpdest` would be
        already constrained to a single concrete value.
        """
        should_check_jumpdest = self._check_jumpdest
        if issymbolic(should_check_jumpdest):
            should_check_jumpdest_solutions = Z3Solver().get_all_values(
                self.constraints, should_check_jumpdest
            )
            if len(should_check_jumpdest_solutions) != 1:
                raise EthereumError("Conditional not concretized at JMPDEST check")
            should_check_jumpdest = should_check_jumpdest_solutions[0]

        # If it can be solved only to False just set it False. If it can be solved
        # only to True, process it and also se it to False
        self._check_jumpdest = False

        if should_check_jumpdest:
            pc = self.pc.value if isinstance(self.pc, Constant) else self.pc
            if pc not in self._valid_jumpdests:
                raise InvalidOpcode()

    def _advance(self, result=None, exception=False):
        if self._checkpoint_data is None:
            return
        last_pc, last_gas, last_instruction, last_arguments, fee, allocated = self._checkpoint_data
        if not exception:
            if not last_instruction.is_branch:
                # advance pc pointer
                self.pc += last_instruction.size
            self._push_results(last_instruction, result)
        self._publish("did_evm_execute_instruction", last_instruction, last_arguments, result)
        self._checkpoint_data = None
        self._published_pre_instruction_events = False

    def change_last_result(self, result):
        last_pc, last_gas, last_instruction, last_arguments, fee, allocated = self._checkpoint_data

        # Check result (push)\
        if last_instruction.pushes > 1:
            assert len(result) == last_instruction.pushes
            for _ in range(last_instruction.pushes):
                self._pop()
            for value in reversed(result):
                self._push(value)
        elif last_instruction.pushes == 1:
            self._pop()
            self._push(result)
        else:
            assert last_instruction.pushes == 0
            assert result is None

    # Execute an instruction from current pc
    def execute(self):
        pc = self.pc
        if issymbolic(pc) and not isinstance(pc, Constant):
            expression = pc
            taints = self.pc.taint

            def setstate(state, value):
                if taints:
                    state.platform.current_vm.pc = BitVecConstant(256, value, taint=taints)
                else:
                    state.platform.current_vm.pc = value

            raise Concretize(
                "Concretize PC", expression=expression, setstate=setstate, policy="ALL"
            )
        # print (self)
        try:
            # import time
            # limbo = 0.0
            # a = time.time()
            self._check_jmpdest()
            # b = time.time()
            last_pc, last_gas, instruction, arguments, fee, allocated = self._checkpoint()
            # c = time.time()
            # d = time.time()
            result = self._handler(*arguments)
            # e = time.time()
            self._advance(result)
            # f = time.time()
            # if hasattr(self, 'F'):
            #    limbo = (a-self.F)*100
            # print(f"{instruction}\t\t %02.4f %02.4f %02.4f %02.4f %02.4f %02.4f"%((b-a)*100, (c-b)*100, (d-c)*100, (e-d)*100, (f-e)*100, limbo))
            # self.F = time.time()

        except ConcretizeGas as ex:

            def setstate(state, value):
                state.platform.current._gas = value

            raise Concretize(
                "Concretize gas", expression=self._gas, setstate=setstate, policy="MINMAX"
            )
        except ConcretizeFee as ex:

            def setstate(state, value):
                current_vm = state.platform.current_vm
                _pc, _old_gas, _instruction, _arguments, _fee, _allocated = (
                    current_vm._checkpoint_data
                )
                current_vm._checkpoint_data = (
                    _pc,
                    _old_gas,
                    _instruction,
                    _arguments,
                    value,
                    _allocated,
                )

            raise Concretize(
                "Concretize current instruction fee",
                expression=fee,
                setstate=setstate,
                policy=ex.policy,
            )
        except ConcretizeArgument as ex:
            pos = ex.pos - 1

            def setstate(state, value):
                current_vm = state.platform.current_vm
                _pc, _old_gas, _instruction, _arguments, _fee, _allocated = (
                    current_vm._checkpoint_data
                )
                new_arguments = []
                for old_arg in _arguments:
                    if len(new_arguments) == pos:
                        new_arguments.append(value)
                    else:
                        new_arguments.append(old_arg)
                current_vm._checkpoint_data = (
                    _pc,
                    _old_gas,
                    _instruction,
                    new_arguments,
                    _fee,
                    _allocated,
                )

            raise Concretize(
                "Concretize Instruction Argument",
                expression=arguments[pos],
                setstate=setstate,
                policy=ex.policy,
            )

        except StartTx:
            raise
        except EndTx as ex:
            self._advance(exception=True)
            raise

    def read_buffer(self, offset, size):
        if issymbolic(size):
            raise EVMException("Symbolic size not supported")
        if size == 0:
            return b""
        self._allocate(offset, size)
        return self.memory[offset : offset + size]

    def write_buffer(self, offset, data):
        self._allocate(offset, len(data))
        for i, c in enumerate(data):
            self._store(offset + i, Operators.ORD(c))

    def _load(self, offset, size=1):
        value = self.memory.read_BE(offset, size)
        try:
            value = simplify(value)
            if not value.taint:
                value = value.value
        except Exception:
            pass

        for i in range(size):
            self._publish(
                "did_evm_read_memory", offset + i, Operators.EXTRACT(value, (size - i - 1) * 8, 8)
            )
        return value

    def _store(self, offset, value, size=1):
        """Stores value in memory as a big endian"""
        self.memory.write_BE(offset, value, size)
        for i in range(size):
            self._publish(
                "did_evm_write_memory", offset + i, Operators.EXTRACT(value, (size - i - 1) * 8, 8)
            )

    def safe_add(self, a, b):
        a = Operators.ZEXTEND(a, 512)
        b = Operators.ZEXTEND(b, 512)
        result = a + b
        return result

    def safe_mul(self, a, b):
        a = Operators.ZEXTEND(a, 512)
        b = Operators.ZEXTEND(b, 512)
        result = a * b
        return result

    ############################################################################
    # INSTRUCTIONS

    def INVALID(self):
        """Halts execution"""
        raise InvalidOpcode()

    ############################################################################
    # Stop and Arithmetic Operations
    # All arithmetic is modulo 256 unless otherwise noted.

    def STOP(self):
        """Halts execution"""
        raise EndTx("STOP")

    def ADD(self, a, b):
        """Addition operation"""
        return a + b

    def MUL(self, a, b):
        """Multiplication operation"""
        return a * b

    def SUB(self, a, b):
        """Subtraction operation"""
        return a - b

    def DIV(self, a, b):
        """Integer division operation"""
        try:
            result = Operators.UDIV(a, b)
        except ZeroDivisionError:
            result = 0
        return Operators.ITEBV(256, b == 0, 0, result)

    def SDIV(self, a, b):
        """Signed integer division operation (truncated)"""
        s0, s1 = to_signed(a), to_signed(b)
        try:
            result = (
                Operators.ABS(s0)
                // Operators.ABS(s1)
                * Operators.ITEBV(256, (s0 < 0) != (s1 < 0), -1, 1)
            )
        except ZeroDivisionError:
            result = 0
        result = Operators.ITEBV(256, b == 0, 0, result)
        if not issymbolic(result):
            result = to_signed(result)
        return result

    def MOD(self, a, b):
        """Modulo remainder operation"""
        try:
            result = Operators.ITEBV(256, b == 0, 0, a % b)
        except ZeroDivisionError:
            result = 0
        return result

    def SMOD(self, a, b):
        """Signed modulo remainder operation"""
        s0, s1 = to_signed(a), to_signed(b)
        sign = Operators.ITEBV(256, s0 < 0, -1, 1)
        try:
            result = (Operators.ABS(s0) % Operators.ABS(s1)) * sign
        except ZeroDivisionError:
            result = 0

        return Operators.ITEBV(256, s1 == 0, 0, result)

    def ADDMOD(self, a, b, c):
        """Modulo addition operation"""
        try:
            result = Operators.ITEBV(256, c == 0, 0, (a + b) % c)
        except ZeroDivisionError:
            result = 0
        return result

    def MULMOD(self, a, b, c):
        """Modulo addition operation"""
        try:
            result = Operators.ITEBV(256, c == 0, 0, (a * b) % c)
        except ZeroDivisionError:
            result = 0
        return result

    def EXP_gas(self, base, exponent):
        """Calculate extra gas fee"""
        EXP_SUPPLEMENTAL_GAS = 10  # cost of EXP exponent per byte

        def nbytes(e):
            result = 0
            for i in range(32):
                result = Operators.ITEBV(512, Operators.EXTRACT(e, i * 8, 8) != 0, i + 1, result)
            return result

        return EXP_SUPPLEMENTAL_GAS * nbytes(exponent)

    @concretized_args(base="SAMPLED", exponent="SAMPLED")
    def EXP(self, base, exponent):
        """
        Exponential operation
        The zero-th power of zero 0^0 is defined to be one.

        :param base: exponential base, concretized with sampled values
        :param exponent: exponent value, concretized with sampled values
        :return: BitVec* EXP result
        """
        if exponent == 0:
            return 1

        if base == 0:
            return 0

        return pow(base, exponent, TT256)

    def SIGNEXTEND(self, size, value):
        """Extend length of two's complement signed integer"""
        # FIXME maybe use Operators.SEXTEND
        testbit = Operators.ITEBV(256, size <= 31, size * 8 + 7, 257)
        result1 = value | (TT256 - (1 << testbit))
        result2 = value & ((1 << testbit) - 1)
        result = Operators.ITEBV(256, (value & (1 << testbit)) != 0, result1, result2)
        return Operators.ITEBV(256, size <= 31, result, value)

    ############################################################################
    # Comparison & Bitwise Logic Operations
    def LT(self, a, b):
        """Less-than comparison"""
        return Operators.ITEBV(256, Operators.ULT(a, b), 1, 0)

    def GT(self, a, b):
        """Greater-than comparison"""
        return Operators.ITEBV(256, Operators.UGT(a, b), 1, 0)

    def SLT(self, a, b):
        """Signed less-than comparison"""
        # http://gavwood.com/paper.pdf
        s0, s1 = to_signed(a), to_signed(b)
        return Operators.ITEBV(256, s0 < s1, 1, 0)

    def SGT(self, a, b):
        """Signed greater-than comparison"""
        # http://gavwood.com/paper.pdf
        s0, s1 = to_signed(a), to_signed(b)
        return Operators.ITEBV(256, s0 > s1, 1, 0)

    def EQ(self, a, b):
        """Equality comparison"""
        return Operators.ITEBV(256, a == b, 1, 0)

    def ISZERO(self, a):
        """Simple not operator"""
        return Operators.ITEBV(256, a == 0, 1, 0)

    def AND(self, a, b):
        """Bitwise AND operation"""
        return a & b

    def OR(self, a, b):
        """Bitwise OR operation"""
        return a | b

    def XOR(self, a, b):
        """Bitwise XOR operation"""
        return a ^ b

    def NOT(self, a):
        """Bitwise NOT operation"""
        return ~a

    def BYTE(self, offset, value):
        """Retrieve single byte from word"""
        offset = Operators.ITEBV(256, offset < 32, (31 - offset) * 8, 256)
        return Operators.ZEXTEND(Operators.EXTRACT(value, offset, 8), 256)

    def try_simplify_to_constant(self, data):
        concrete_data = bytearray()
        for c in data:
            simplified = simplify(c)
            if isinstance(simplified, Constant):
                concrete_data.append(simplified.value)
            else:
                # simplify by solving. probably means that we need to improve simplification
                solutions = Z3Solver.instance().get_all_values(
                    self.constraints, simplified, 2, silent=True
                )
                if len(solutions) != 1:
                    break
                concrete_data.append(solutions[0])
        else:
            data = bytes(concrete_data)
        return data

    def SHA3_gas(self, start, size):
        GSHA3WORD = 6  # Cost of SHA3 per word
        memfee = self._get_memfee(start, size)
        return GSHA3WORD * (ceil32(size) // 32) + memfee

    @concretized_args(size="SAMPLED")
    def SHA3(self, start, size):
        """Compute Keccak-256 hash"""
        # read memory from start to end
        # http://gavwood.com/paper.pdf
        data = self.try_simplify_to_constant(self.read_buffer(start, size))

        if issymbolic(data):
            known_sha3 = {}
            # Broadcast the signal
            self._publish(
                "on_symbolic_sha3", data, known_sha3
            )  # This updates the local copy of sha3 with the pairs we need to explore
            value = 0  # never used
            known_hashes_cond = False
            for key, hsh in known_sha3.items():
                assert not issymbolic(key), "Saved sha3 data,hash pairs should be concrete"
                cond = key == data
                known_hashes_cond = Operators.OR(cond, known_hashes_cond)
                value = Operators.ITEBV(256, cond, hsh, value)
            return value

        value = sha3.keccak_256(data).hexdigest()
        value = int(value, 16)
        self._publish("on_concrete_sha3", data, value)
        logger.info("Found a concrete SHA3 example %r -> %x", data, value)
        return value

    ############################################################################
    # Environmental Information
    def ADDRESS(self):
        """Get address of currently executing account"""
        return self.address

    def BALANCE_gas(self, account):
        return 380  # BALANCE_SUPPLEMENTAL_GAS

    def BALANCE(self, account):
        """Get balance of the given account"""
        return self.world.get_balance(account)

    def ORIGIN(self):
        """Get execution origination address"""
        return Operators.ZEXTEND(self.world.tx_origin(), 256)

    def CALLER(self):
        """Get caller address"""
        return Operators.ZEXTEND(self.caller, 256)

    def CALLVALUE(self):
        """Get deposited value by the instruction/transaction responsible for this execution"""
        return self.value

    def CALLDATALOAD(self, offset):
        """Get input data of current environment"""

        if issymbolic(offset):
            if Z3Solver().can_be_true(self._constraints, offset == self._used_calldata_size):
                self.constraints.add(offset == self._used_calldata_size)
            raise ConcretizeArgument(1, policy="SAMPLED")

        self._use_calldata(offset, 32)

        data_length = len(self.data)

        bytes = []
        for i in range(32):
            try:
                c = Operators.ITEBV(8, offset + i < data_length, self.data[offset + i], 0)
            except IndexError:
                # offset + i is concrete and outside data
                c = 0

            bytes.append(c)
        return Operators.CONCAT(256, *bytes)

    def _use_calldata(self, n, size):
        assert not issymbolic(n)
        max_size = len(self.data)
        min_size = self._used_calldata_size
        self._used_calldata_size = Operators.ITEBV(
            256,
            size != 0,
            Operators.ITEBV(256, min_size + n > max_size, max_size, min_size + n),
            self._used_calldata_size,
        )

    def CALLDATASIZE(self):
        """Get size of input data in current environment"""
        return self._calldata_size

    def CALLDATACOPY_gas(self, mem_offset, data_offset, size):
        GCOPY = 3  # cost to copy one 32 byte word
        copyfee = self.safe_mul(GCOPY, self.safe_add(size, 31) // 32)
        memfee = self._get_memfee(mem_offset, size)
        return copyfee + memfee

    def CALLDATACOPY(self, mem_offset, data_offset, size):
        """Copy input data in current environment to memory"""
        if issymbolic(size):
            if Z3Solver().can_be_true(self._constraints, size <= len(self.data) + 32):
                self.constraints.add(size <= len(self.data) + 32)
            raise ConcretizeArgument(3, policy="SAMPLED")

        if issymbolic(data_offset):
            if Z3Solver().can_be_true(self._constraints, data_offset == self._used_calldata_size):
                self.constraints.add(data_offset == self._used_calldata_size)
            raise ConcretizeArgument(2, policy="SAMPLED")

        # account for calldata usage
        self._use_calldata(data_offset, size)
        self._allocate(mem_offset, size)
        for i in range(size):
            try:
                c = Operators.ITEBV(
                    8,
                    data_offset + i < len(self.data),
                    Operators.ORD(self.data[data_offset + i]),
                    0,
                )
            except IndexError:
                # data_offset + i is concrete and outside data
                c = 0
            self._store(mem_offset + i, c)

    def CODESIZE(self):
        """Get size of code running in current environment"""
        return len(self.bytecode)

    def CODECOPY_gas(self, mem_offset, code_offset, size):
        return self._get_memfee(mem_offset, size)

    @concretized_args(code_offset="SAMPLED", size="SAMPLED")
    def CODECOPY(self, mem_offset, code_offset, size):
        """Copy code running in current environment to memory"""

        self._allocate(mem_offset, size)
        GCOPY = 3  # cost to copy one 32 byte word
        copyfee = self.safe_mul(GCOPY, Operators.UDIV(self.safe_add(size, 31), 32))
        self._consume(copyfee)

        if issymbolic(size):
            max_size = Z3Solver().max(self.constraints, size)
        else:
            max_size = size

        for i in range(max_size):
            if issymbolic(i < size):
                default = Operators.ITEBV(
                    8, i < size, 0, self._load(mem_offset + i, 1)
                )  # Fixme. unnecessary memory read
            else:
                if i < size:
                    default = 0
                else:
                    default = self._load(mem_offset + i, 1)

            if issymbolic(code_offset):
                value = Operators.ITEBV(
                    8,
                    code_offset + i >= len(self.bytecode),
                    default,
                    self.bytecode[code_offset + i],
                )
            else:
                if code_offset + i >= len(self.bytecode):
                    value = default
                else:
                    value = self.bytecode[code_offset + i]
            self._store(mem_offset + i, value)
        self._publish("did_evm_read_code", code_offset, size)

    def GASPRICE(self):
        """Get price of gas in current environment"""
        return self.world.tx_gasprice()

    @concretized_args(account="ACCOUNTS")
    def EXTCODESIZE(self, account):
        """Get size of an account's code"""
        return len(self.world.get_code(account))

    def EXTCODECOPY_gas(self, account, address, offset, size):
        GCOPY = 3  # cost to copy one 32 byte word
        extbytecode = self.world.get_code(account)
        memfee = self._get_memfee(address, size)
        return GCOPY * (ceil32(len(extbytecode)) // 32) + memfee

    @concretized_args(account="ACCOUNTS")
    def EXTCODECOPY(self, account, address, offset, size):
        """Copy an account's code to memory"""
        extbytecode = self.world.get_code(account)
        self._allocate(address + size)

        for i in range(size):
            if offset + i < len(extbytecode):
                self._store(address + i, extbytecode[offset + i])
            else:
                self._store(address + i, 0)

    def RETURNDATACOPY_gas(self, mem_offset, return_offset, size):
        return self._get_memfee(mem_offset, size)

    def RETURNDATACOPY(self, mem_offset, return_offset, size):
        return_data = self.world.last_transaction.return_data

        self._allocate(mem_offset, size)
        for i in range(size):
            if return_offset + i < len(return_data):
                self._store(mem_offset + i, return_data[return_offset + i])
            else:
                self._store(mem_offset + i, 0)

    def RETURNDATASIZE(self):
        return len(self.world.last_transaction.return_data)

    ############################################################################
    # Block Information
    def BLOCKHASH(self, a):
        """Get the hash of one of the 256 most recent complete blocks"""
        return self.world.block_hash(a)

    def COINBASE(self):
        """Get the block's beneficiary address"""
        return self.world.block_coinbase()

    def TIMESTAMP(self):
        """Get the block's timestamp"""
        return self.world.block_timestamp()

    def NUMBER(self):
        """Get the block's number"""
        return self.world.block_number()

    def DIFFICULTY(self):
        """Get the block's difficulty"""
        return self.world.block_difficulty()

    def GASLIMIT(self):
        """Get the block's gas limit"""
        return self.world.block_gaslimit()

    ############################################################################
    # Stack, Memory, Storage and Flow Operations
    def POP(self, a):
        """Remove item from stack"""
        # Items are automatically removed from stack
        # by the instruction dispatcher
        pass

    def MLOAD_gas(self, address):
        return self._get_memfee(address, 32)

    def MLOAD(self, address):
        """Load word from memory"""
        self._allocate(address, 32)
        value = self._load(address, 32)
        return value

    def MSTORE_gas(self, address, value):
        return self._get_memfee(address, 32)

    def MSTORE(self, address, value):
        """Save word to memory"""
        if istainted(self.pc):
            for taint in get_taints(self.pc):
                value = taint_with(value, taint)
        self._allocate(address, 32)
        self._store(address, value, 32)

    def MSTORE8_gas(self, address, value):
        return self._get_memfee(address, 1)

    def MSTORE8(self, address, value):
        """Save byte to memory"""
        if istainted(self.pc):
            for taint in get_taints(self.pc):
                value = taint_with(value, taint)
        self._allocate(address, 1)
        self._store(address, Operators.EXTRACT(value, 0, 8), 1)

    def SLOAD(self, offset):
        """Load word from storage"""
        storage_address = self.address
        self._publish("will_evm_read_storage", storage_address, offset)
        value = self.world.get_storage_data(storage_address, offset)
        self._publish("did_evm_read_storage", storage_address, offset, value)
        return value

    def SSTORE_gas(self, offset, value):
        storage_address = self.address
        GSTORAGEREFUND = 15000
        GSTORAGEKILL = 5000
        GSTORAGEMOD = 5000
        GSTORAGEADD = 20000

        previous_value = self.world.get_storage_data(storage_address, offset)

        gascost = Operators.ITEBV(
            512,
            previous_value != 0,
            Operators.ITEBV(512, value != 0, GSTORAGEMOD, GSTORAGEKILL),
            Operators.ITEBV(512, value != 0, GSTORAGEADD, GSTORAGEMOD),
        )

        return gascost

    def SSTORE(self, offset, value):
        """Save word to storage"""
        storage_address = self.address
        self._publish("will_evm_write_storage", storage_address, offset, value)
        # refund = Operators.ITEBV(256,
        #                         previous_value != 0,
        #                         Operators.ITEBV(256, value != 0, 0, GSTORAGEREFUND),
        #                         0)

        if istainted(self.pc):
            for taint in get_taints(self.pc):
                value = taint_with(value, taint)
        self.world.set_storage_data(storage_address, offset, value)
        self._publish("did_evm_write_storage", storage_address, offset, value)

    def JUMP(self, dest):
        """Alter the program counter"""
        self.pc = dest
        # This set ups a check for JMPDEST in the next instruction
        self._set_check_jmpdest()

    def JUMPI(self, dest, cond):
        """Conditionally alter the program counter"""
        self.pc = Operators.ITEBV(256, cond != 0, dest, self.pc + self.instruction.size)
        # This set ups a check for JMPDEST in the next instruction if cond != 0
        self._set_check_jmpdest(cond != 0)

    def GETPC(self):
        """Get the value of the program counter prior to the increment"""
        return self.pc

    def MSIZE(self):
        """Get the size of active memory in bytes"""
        return self._allocated

    def GAS(self):
        """Get the amount of available gas, including the corresponding reduction the amount of available gas"""
        # fixme calculate gas consumption
        return Operators.EXTRACT(self._gas, 0, 256)

    def JUMPDEST(self):
        """Mark a valid destination for jumps"""

    ############################################################################
    # Push Operations
    def PUSH(self, value):
        """Place 1 to 32 bytes item on stack"""
        return value

    ############################################################################
    # Duplication Operations
    def DUP(self, *operands):
        """Duplicate stack item"""
        return (operands[-1],) + operands

    ############################################################################
    # Exchange Operations
    def SWAP(self, *operands):
        """Exchange 1st and 2nd stack items"""
        a = operands[0]
        b = operands[-1]
        return (b,) + operands[1:-1] + (a,)

    ############################################################################
    # Logging Operations
    def LOG_gas(self, address, size, *topics):
        return self._get_memfee(address, size)

    @concretized_args(size="ONE")
    def LOG(self, address, size, *topics):
        GLOGBYTE = 8
        self._consume(size * GLOGBYTE)
        memlog = self.read_buffer(address, size)
        self.world.log(self.address, topics, memlog)

    ############################################################################
    # System operations
    def CREATE_gas(self, value, offset, size):
        return self._get_memfee(offset, size)

    @transact
    def CREATE(self, value, offset, size):
        """Create a new account with associated code"""
        address = self.world.create_account(
            address=EVMWorld.calculate_new_address(
                sender=self.address, nonce=self.world.get_nonce(self.address)
            )
        )
        self.world.start_transaction(
            "CREATE",
            address,
            data=self.read_buffer(offset, size),
            caller=self.address,
            value=value,
            gas=self.gas,
        )

        raise StartTx()

    @CREATE.pos
    def CREATE(self, value, offset, size):
        """Create a new account with associated code"""
        tx = self.world.last_transaction  # At this point last and current tx are the same.
        address = tx.address
        if tx.result == "RETURN":
            self.world.set_code(tx.address, tx.return_data)
        else:
            self.world.delete_account(address)
            address = 0
        return address

    def CALL_gas(self, gas, address, value, in_offset, in_size, out_offset, out_size):
        return self._get_memfee(in_offset, in_size)

    @transact
    @concretized_args(address="ACCOUNTS", gas="MINMAX", in_offset="SAMPLED", in_size="SAMPLED")
    def CALL(self, gas, address, value, in_offset, in_size, out_offset, out_size):
        """Message-call into an account"""
        self.world.start_transaction(
            "CALL",
            address,
            data=self.read_buffer(in_offset, in_size),
            caller=self.address,
            value=value,
            gas=gas,
        )
        raise StartTx()

    @CALL.pos
    def CALL(self, gas, address, value, in_offset, in_size, out_offset, out_size):
        data = self.world.last_transaction.return_data
        if data is not None:
            data_size = len(data)
            size = Operators.ITEBV(256, Operators.ULT(out_size, data_size), out_size, data_size)
            self.write_buffer(out_offset, data[:size])

        return self.world.last_transaction.return_value

    def CALLCODE_gas(self, gas, address, value, in_offset, in_size, out_offset, out_size):
        return self._get_memfee(in_offset, in_size)

    @transact
    @concretized_args(in_offset="SAMPLED", in_size="SAMPLED")
    def CALLCODE(self, gas, _ignored_, value, in_offset, in_size, out_offset, out_size):
        """Message-call into this account with alternative account's code"""
        self.world.start_transaction(
            "CALLCODE",
            address=self.address,
            data=self.read_buffer(in_offset, in_size),
            caller=self.address,
            value=value,
            gas=gas,
        )
        raise StartTx()

    @CALLCODE.pos
    def CALLCODE(self, gas, address, value, in_offset, in_size, out_offset, out_size):
        data = self.world.last_transaction.return_data
        if data is not None:
            data_size = len(data)
            size = Operators.ITEBV(256, Operators.ULT(out_size, data_size), out_size, data_size)
            self.write_buffer(out_offset, data[:size])

        return self.world.last_transaction.return_value

    def RETURN_gas(self, offset, size):
        return self._get_memfee(offset, size)

    @concretized_args(size="SAMPLED")
    def RETURN(self, offset, size):
        """Halt execution returning output data"""
        data = self.read_buffer(offset, size)
        raise EndTx("RETURN", data)

    def DELEGATECALL_gas(self, gas, address, in_offset, in_size, out_offset, out_size):
        return self._get_memfee(in_offset, in_size)

    @transact
    @concretized_args(in_offset="SAMPLED", in_size="SAMPLED")
    def DELEGATECALL(self, gas, address, in_offset, in_size, out_offset, out_size):
        """Message-call into an account"""
        self.world.start_transaction(
            "DELEGATECALL",
            address,
            data=self.read_buffer(in_offset, in_size),
            caller=self.address,
            value=0,
            gas=gas,
        )
        raise StartTx()

    @DELEGATECALL.pos
    def DELEGATECALL(self, gas, address, in_offset, in_size, out_offset, out_size):
        data = self.world.last_transaction.return_data
        if data is not None:
            data_size = len(data)
            size = Operators.ITEBV(256, Operators.ULT(out_size, data_size), out_size, data_size)
            self.write_buffer(out_offset, data[:size])

        return self.world.last_transaction.return_value

    def STATICCALL_gas(self, gas, address, in_offset, in_size, out_offset, out_size):
        return self._get_memfee(in_offset, in_size)

    @transact
    @concretized_args(in_offset="SAMPLED", in_size="SAMPLED")
    def STATICCALL(self, gas, address, in_offset, in_size, out_offset, out_size):
        """Message-call into an account"""
        self.world.start_transaction(
            "STATICCALL",
            address,
            data=self.read_buffer(in_offset, in_size),
            caller=self.address,
            value=0,
            gas=gas,
        )
        raise StartTx()

    @STATICCALL.pos
    def STATICCALL(self, gas, address, in_offset, in_size, out_offset, out_size):
        data = self.world.last_transaction.return_data
        if data is not None:
            data_size = len(data)
            size = Operators.ITEBV(256, Operators.ULT(out_size, data_size), out_size, data_size)
            self.write_buffer(out_offset, data[:size])

        return self.world.last_transaction.return_value

    def REVERT_gas(self, offset, size):
        return self._get_memfee(offset, size)

    def REVERT(self, offset, size):
        data = self.read_buffer(offset, size)
        # FIXME return remaining gas
        raise EndTx("REVERT", data)

    def THROW(self):
        # revert balance on CALL fail
        raise EndTx("THROW")

    def SELFDESTRUCT(self, recipient):
        """Halt execution and register account for later deletion"""
        # This may create a user account
        recipient = Operators.EXTRACT(recipient, 0, 160)
        address = self.address
        # FIXME for on the known addresses
        if issymbolic(recipient):
            logger.info("Symbolic recipient on self destruct")
            recipient = Z3Solver().get_value(self.constraints, recipient)

        if recipient not in self.world:
            self.world.create_account(address=recipient)

        self.world.send_funds(address, recipient, self.world.get_balance(address))
        self.world.delete_account(address)

        raise EndTx("SELFDESTRUCT")

    def __str__(self):
        m = []
        for offset in range(128):
            c = simplify(self.memory[offset])
            try:
                c = c.value
            except Exception:
                pass
            m.append(c)

        hd = _hexdump(m)

        result = ["-" * 147]
        pc = self.pc
        if isinstance(pc, Constant):
            pc = pc.value

        if issymbolic(pc):
            result.append("<Symbolic PC> {:s} {}\n".format(translate_to_smtlib(pc), pc.taint))
        else:
            operands_str = (
                self.instruction.has_operand and "0x{:x}".format(self.instruction.operand) or ""
            )
            result.append(
                "0x{:04x}: {:s} {:s} {:s}".format(
                    pc, self.instruction.name, operands_str, self.instruction.description
                )
            )

        args = {}
        implementation = getattr(self, self.instruction.semantics, None)
        if implementation is not None:
            args = dict(
                enumerate(
                    inspect.getfullargspec(implementation).args[1 : self.instruction.pops + 1]
                )
            )

        clmn = 80
        result.append(
            "Stack                                                                           Memory"
        )
        sp = 0
        for i in list(reversed(self.stack))[:10]:
            argname = args.get(sp, "top" if sp == 0 else "")
            r = ""
            if issymbolic(i):
                r = "{:>12s} {:66s}".format(argname, repr(i))
            else:
                r = "{:>12s} 0x{:064x}".format(argname, i)
            sp += 1

            h = ""
            try:
                h = hd[sp - 1]
            except BaseException:
                pass
            r += " " * (clmn - len(r)) + h
            result.append(r)

        for i in range(sp, len(hd)):
            r = " " * clmn + hd[i]
            result.append(r)

        # Append gas
        gas = self.gas
        if issymbolic(gas):
            gas = simplify(gas)
            result.append(f"Gas: {translate_to_smtlib(gas)} {gas.taint}")
        else:
            result.append(f"Gas: {gas}")

        return "\n".join(hex(self.address) + ": " + x for x in result)


################################################################################
################################################################################
################################################################################
################################################################################


class EVMWorld(Platform):
    _published_events = {
        "evm_read_storage",
        "evm_write_storage",
        "evm_read_code",
        "decode_instruction",
        "execute_instruction",
        "concrete_sha3",
        "symbolic_sha3",
        "open_transaction",
        "close_transaction",
    }

    def __init__(
        self,
        constraints,
        storage=None,
        blocknumber=None,
        timestamp=None,
        difficulty=0,
        gaslimit=0,
        coinbase=0,
        **kwargs,
    ):
        super().__init__(path="NOPATH", **kwargs)
        self._world_state = {} if storage is None else storage
        self._constraints = constraints
        self._callstack: List[
            Tuple[Transaction, List[EVMLog], Set[int], Union[bytearray, ArrayProxy], EVM]
        ] = []
        self._deleted_accounts: Set[int] = set()
        self._logs: List[EVMLog] = list()
        self._pending_transaction = None
        self._transactions: List[Transaction] = list()

        if blocknumber is None:
            # assume initial byzantium block
            blocknumber = 4370000
        self._blocknumber = blocknumber

        if timestamp is None:
            # 1524785992; // Thu Apr 26 23:39:52 UTC 2018
            timestamp = 1524785992
        self._timestamp = timestamp

        self._difficulty = difficulty
        self._gaslimit = gaslimit
        self._coinbase = coinbase

    def __getstate__(self):
        state = super().__getstate__()
        state["pending_transaction"] = self._pending_transaction
        state["logs"] = self._logs
        state["world_state"] = self._world_state
        state["constraints"] = self._constraints
        state["callstack"] = self._callstack
        state["deleted_accounts"] = self._deleted_accounts
        state["transactions"] = self._transactions
        state["_blocknumber"] = self._blocknumber
        state["_timestamp"] = self._timestamp
        state["_difficulty"] = self._difficulty
        state["_gaslimit"] = self._gaslimit
        state["_coinbase"] = self._coinbase
        return state

    def __setstate__(self, state):
        super().__setstate__(state)
        self._constraints = state["constraints"]
        self._pending_transaction = state["pending_transaction"]
        self._world_state = state["world_state"]
        self._deleted_accounts = state["deleted_accounts"]
        self._logs = state["logs"]
        self._callstack = state["callstack"]
        self._transactions = state["transactions"]
        self._blocknumber = state["_blocknumber"]
        self._timestamp = state["_timestamp"]
        self._difficulty = state["_difficulty"]
        self._gaslimit = state["_gaslimit"]
        self._coinbase = state["_coinbase"]

        for _, _, _, _, vm in self._callstack:
            self.forward_events_from(vm)

    @property
    def PC(self):
        return (self.current_vm.address, self.current_vm.pc)

    def __getitem__(self, index):
        assert isinstance(index, int)
        return self._world_state[index]

    def __contains__(self, key):
        assert not issymbolic(key), "Symbolic address not supported"
        return key in self.accounts

    def __str__(self):
        return "WORLD:" + str(self._world_state)

    @property
    def logs(self):
        return self._logs

    @property
    def constraints(self):
        return self._constraints

    def _open_transaction(self, sort, address, price, bytecode_or_data, caller, value, gas=2300):
        if self.depth > 0:
            origin = self.tx_origin()
        else:
            origin = caller
        assert price is not None

        tx = Transaction(
            sort, address, price, bytecode_or_data, caller, value, depth=self.depth, gas=gas
        )
        if sort == "CREATE":
            bytecode = bytecode_or_data
            data = bytearray()
        else:
            bytecode = self.get_code(address)
            data = bytecode_or_data

        if tx.sort == "DELEGATECALL":
            # So at a DELEGATECALL the environment should look exactly the same as the original tx
            # This means caller, value and address are the same as prev tx
            assert value == 0
            address = self.current_transaction.address
            caller = self.current_transaction.caller
            value = self.current_transaction.value

        vm = EVM(self._constraints, address, data, caller, value, bytecode, world=self, gas=gas)

        self._publish("will_open_transaction", tx)
        self._callstack.append(
            (tx, self.logs, self.deleted_accounts, copy.copy(self.get_storage(address)), vm)
        )
        self.forward_events_from(vm)
        self._publish("did_open_transaction", tx)

    def _close_transaction(self, result, data=None, rollback=False):
        self._publish("will_close_transaction", self._callstack[-1][0])
        tx, logs, deleted_accounts, account_storage, vm = self._callstack.pop()
        assert self.constraints == vm.constraints
        # Keep constraints gathered in the last vm
        self.constraints = vm.constraints
        if rollback:
            self._set_storage(vm.address, account_storage)
            self._logs = logs
            self.send_funds(tx.address, tx.caller, tx.value)
        else:
            self._deleted_accounts = deleted_accounts

            # FIXME: BUG: a CREATE can be successful and still return an empty contract :shrug:
            if not issymbolic(tx.caller) and (
                tx.sort == "CREATE" or not self._world_state[tx.caller]["code"]
            ):
                # Increment the nonce if this transaction created a contract, or if it was called by a non-contract account
                self.increase_nonce(tx.caller)

        if tx.is_human:
            for deleted_account in self._deleted_accounts:
                if deleted_account in self._world_state:
                    del self._world_state[deleted_account]
        tx.set_result(result, data)
        self._transactions.append(tx)

        self._publish("did_close_transaction", tx)

        if self.depth == 0:
            raise TerminateState(tx.result)

    @property
    def all_transactions(self):
        txs = tuple(self._transactions)
        return txs + tuple((x[0] for x in reversed(self._callstack)))

    @property
    def transactions(self):
        """Completed completed transaction"""
        return tuple((tx for tx in self._transactions if tx.result != "TXERROR"))

    @property
    def human_transactions(self):
        """Completed human transaction"""
        txs = []
        for tx in self.transactions:
            if tx.depth == 0:
                txs.append(tx)
        return tuple(txs)

    @property
    def last_transaction(self):
        """Last completed transaction"""
        if len(self.transactions):
            return self.transactions[-1]
        return None

    @property
    def last_human_transaction(self):
        """Last completed human transaction"""
        for tx in reversed(self.transactions):
            if tx.depth == 0:
                return tx
        return None

    @constraints.setter
    def constraints(self, constraints):
        self._constraints = constraints
        if self.current_vm:
            self.current_vm.constraints = constraints

    @property
    def current_vm(self):
        """current vm"""
        try:
            _, _, _, _, vm = self._callstack[-1]
            return vm
        except IndexError:
            return None

    @property
    def current_transaction(self):
        """current tx"""
        try:
            tx, _, _, _, _ = self._callstack[-1]
            if tx.result is not None:
                # That tx finished. No current tx.
                return None
            return tx
        except IndexError:
            return None

    @property
    def current_human_transaction(self):
        """Current ongoing human transaction"""
        try:
            tx, _, _, _, _ = self._callstack[0]
            if tx.result is not None:
                # That tx finished. No current tx.
                return None
            assert tx.depth == 0
            return tx
        except IndexError:
            return None

    @property
    def accounts(self):
        return list(self._world_state.keys())

    @property
    def normal_accounts(self):
        accs = []
        for address in self.accounts:
            if len(self.get_code(address)) == 0:
                accs.append(address)
        return accs

    @property
    def contract_accounts(self):
        accs = []
        for address in self.accounts:
            if len(self.get_code(address)) > 0:
                accs.append(address)
        return accs

    @property
    def deleted_accounts(self):
        return self._deleted_accounts

    def delete_account(self, address):
        if address in self._world_state:
            self._deleted_accounts.add(address)

    def get_storage_data(self, storage_address, offset):
        """
        Read a value from a storage slot on the specified account

        :param storage_address: an account address
        :param offset: the storage slot to use.
        :type offset: int or BitVec
        :return: the value
        :rtype: int or BitVec
        """
        value = self._world_state[storage_address]["storage"].get(offset, 0)
        return simplify(value)

    def set_storage_data(self, storage_address, offset, value):
        """
        Writes a value to a storage slot in specified account

        :param storage_address: an account address
        :param offset: the storage slot to use.
        :type offset: int or BitVec
        :param value: the value to write
        :type value: int or BitVec
        """
        self._world_state[storage_address]["storage"][offset] = value

    def get_storage_items(self, address):
        """
        Gets all items in an account storage

        :param address: account address
        :return: all items in account storage. items are tuple of (index, value). value can be symbolic
        :rtype: list[(storage_index, storage_value)]
        """
        storage = self._world_state[address]["storage"]
        items = []
        array = storage.array
        while not isinstance(array, ArrayVariable):
            items.append((array.index, array.value))
            array = array.array
        return items

    def has_storage(self, address):
        """
        True if something has been written to the storage.
        Note that if a slot has been erased from the storage this function may
        lose any meaning.
        """
        storage = self._world_state[address]["storage"]
        array = storage.array
        while not isinstance(array, ArrayVariable):
            if isinstance(array, ArrayStore):
                return True
            array = array.array
        return False

    def get_storage(self, address):
        """
        Gets the storage of an account

        :param address: account address
        :return: account storage
        :rtype: bytearray or ArrayProxy
        """
        return self._world_state[address]["storage"]

    def _set_storage(self, address, storage):
        """Private auxiliary function to replace the storage"""
        self._world_state[address]["storage"] = storage

    def get_nonce(self, address):
        if issymbolic(address):
            raise ValueError(f"Cannot retrieve the nonce of symbolic address {address}")
        elif address not in self._world_state:
            # assume that the caller is a regular account, so initialize its nonce to zero
            ret = 0
        elif "nonce" not in self._world_state[address]:
            if self._world_state[address]["code"]:
                # this is a contract account, so set the nonce to 1 per EIP 161
                ret = 1
            else:
                ret = 0
        else:
            ret = self._world_state[address]["nonce"]
        return ret

    def increase_nonce(self, address):
        new_nonce = self.get_nonce(address) + 1
        self._world_state[address]["nonce"] = new_nonce
        return new_nonce

    def set_balance(self, address, value):
        self._world_state[int(address)]["balance"] = value

    def get_balance(self, address):
        if address not in self._world_state:
            return 0
        return self._world_state[address]["balance"]

    def add_to_balance(self, address, value):
        assert address in self._world_state
        self._world_state[address]["balance"] += value

    def send_funds(self, sender, recipient, value):
        self._world_state[sender]["balance"] -= value
        self._world_state[recipient]["balance"] += value

    def get_code(self, address):
        if address not in self._world_state:
            return bytes()
        return self._world_state[address]["code"]

    def set_code(self, address, data):
        assert data is not None and isinstance(data, (bytes, Array))
        if self._world_state[address]["code"]:
            raise EVMException("Code already set")
        self._world_state[address]["code"] = data

    def has_code(self, address):
        return len(self._world_state[address]["code"]) > 0

    def get_nonce(self, address):
        if address not in self._world_state:
            return 0
        return self._world_state[address]["nonce"]

    def log(self, address, topics, data):
        self._logs.append(EVMLog(address, data, topics))
        logger.info("LOG %r %r", data, topics)

    def log_storage(self, addr):
        pass

    def add_refund(self, value):
        pass

    def block_prevhash(self):
        return 0

    def block_coinbase(self):
        return self._coinbase

    def block_timestamp(self):
        return self._timestamp

    def block_number(self):
        return self._blocknumber

    def block_difficulty(self):
        return self._difficulty

    def block_gaslimit(self):
        return self._gaslimit

    def block_hash(self, block_number=None, force_recent=True):
        """
        Calculates a block's hash
        :param block_number: the block number for which to calculate the hash, defaulting to the most recent block
        :param force_recent: if True (the default) return zero for any block that is in the future or older than 256 blocks
        :return: the block hash
        """
        if block_number is None:
            block_number = self.block_number() - 1

        # We are not maintaining an actual -block-chain- so we just generate
        # some hashes for each virtual block
        value = sha3.keccak_256((repr(block_number) + "NONCE").encode()).hexdigest()
        value = int(value, 16)

        if force_recent:
            # 0 is left on the stack if the looked for block number is greater or equal
            # than the current block number or more than 256 blocks behind the current
            # block. (Current block hash is unknown from inside the tx)
            bnmax = Operators.ITEBV(256, self.block_number() > 256, 256, self.block_number())
            value = Operators.ITEBV(
                256,
                Operators.OR(block_number >= self.block_number(), block_number < bnmax),
                0,
                value,
            )

        return value

    def tx_origin(self):
        if self.current_human_transaction:
            return self.current_human_transaction.caller

    def tx_gasprice(self):
        if self.current_human_transaction:
            return self.current_human_transaction.price

    @property
    def depth(self):
        return len(self._callstack)

    def new_address(self, sender=None, nonce=None):
        """Create a fresh 160bit address"""
        if sender is not None and nonce is None:
            nonce = self.get_nonce(sender)

        new_address = self.calculate_new_address(sender, nonce)
        if sender is None and new_address in self:
            return self.new_address(sender, nonce)
        return new_address

    @staticmethod
    def calculate_new_address(sender=None, nonce=None):
        if sender is None:
            # Just choose a random address for regular accounts:
            new_address = random.randint(100, pow(2, 160))
        elif issymbolic(sender):
            # TODO(Evan Sultanik): In the interim before we come up with a better solution,
            #                      consider breaking Yellow Paper comability and just returning
            #                      a random contract address here
            raise EthereumError(
                "Manticore does not yet support contracts with symbolic addresses creating new contracts"
            )
        else:
            if nonce is None:
                # assume that the sender is a contract account, which is initialized with a nonce of 1
                nonce = 1
            new_address = int(sha3.keccak_256(rlp.encode([sender, nonce])).hexdigest()[24:], 16)
        return new_address

    def execute(self):

        self._process_pending_transaction()
        if self.current_vm is None:
            raise TerminateState("Trying to execute an empty transaction", testcase=False)
        try:
            self.current_vm.execute()
        except StartTx:
            pass
        except EndTx as ex:
            self._close_transaction(ex.result, ex.data, rollback=ex.is_rollback())

    def create_account(self, address=None, balance=0, code=None, storage=None, nonce=None):
        """
        Low level account creation. No transaction is done.
        :param address: the address of the account, if known. If omitted, a new address will be generated as closely to the Yellow Paper as possible.
        :param balance: the initial balance of the account in Wei
        :param code: the runtime code of the account, if a contract
        :param storage: storage array
        :param nonce: the nonce for the account; contracts should have a nonce greater than or equal to 1
        """
        if code is None:
            code = bytes()
        else:
            if not isinstance(code, (bytes, Array)):
                raise EthereumError("Wrong code type")

        # nonce default to initial nonce
        if nonce is None:
            # As per EIP 161, contract accounts are initialized with a nonce of 1
            nonce = 1 if code else 0

        if address is None:
            address = self.new_address()

        if not isinstance(address, int):
            raise EthereumError("You must provide an address")

        if address in self.accounts:
            # FIXME account may have been created via selfdestruct destination
            # or CALL and may contain some ether already, though if it was a
            # selfdestructed address, it can not be reused
            raise EthereumError("The account already exists")

        if storage is None:
            # Uninitialized values in a storage are 0 by spec
            storage = self.constraints.new_array(
                index_bits=256,
                value_bits=256,
                name=f"STORAGE_{address:x}",
                avoid_collisions=True,
                default=0,
            )
        else:
            if isinstance(storage, ArrayProxy):
                if storage.index_bits != 256 or storage.value_bits != 256:
                    raise TypeError("An ArrayProxy 256bits -> 256bits is needed")
            else:
                if any((k < 0 or k >= 1 << 256 for k, v in storage.items())):
                    raise TypeError(
                        "Need a dict like object that maps 256 bits keys to 256 bits values"
                    )
            # Hopefully here we have a mapping from 256b to 256b

        self._world_state[address] = {}
        self._world_state[address]["nonce"] = nonce
        self._world_state[address]["balance"] = balance
        self._world_state[address]["storage"] = storage
        self._world_state[address]["code"] = code

        # adds hash of new address
        data = binascii.unhexlify("{:064x}{:064x}".format(address, 0))
        value = sha3.keccak_256(data).hexdigest()
        value = int(value, 16)
        self._publish("on_concrete_sha3", data, value)

        return address

    def create_contract(self, price=0, address=None, caller=None, balance=0, init=None, gas=None):
        """
        Create a contract account. Sends a transaction to initialize the contract

        :param address: the address of the new account, if known. If omitted, a new address will be generated as closely to the Yellow Paper as possible.
        :param balance: the initial balance of the account in Wei
        :param init: the initialization code of the contract

        The way that the Solidity compiler expects the constructor arguments to
        be passed is by appending the arguments to the byte code produced by the
        Solidity compiler. The arguments are formatted as defined in the Ethereum
        ABI2. The arguments are then copied from the init byte array to the EVM
        memory through the CODECOPY opcode with appropriate values on the stack.
        This is done when the byte code in the init byte array is actually run
        on the network.
        """
        expected_address = self.create_account(self.new_address(sender=caller))
        if address is None:
            address = expected_address
        elif caller is not None and address != expected_address:
            raise EthereumError(
                f"Error: contract created from address {hex(caller)} with nonce {self.get_nonce(caller)} was expected to be at address {hex(expected_address)}, but create_contract was called with address={hex(address)}"
            )
        self.start_transaction("CREATE", address, price, init, caller, balance, gas=gas)
        self._process_pending_transaction()
        return address

    def transaction(self, address, price=0, data="", caller=None, value=0, gas=2300):
        self.start_transaction(
            "CALL", address, price=price, data=data, caller=caller, value=value, gas=gas
        )
        self._process_pending_transaction()

    def start_transaction(
        self, sort, address, *, price=None, data=None, caller=None, value=0, gas=2300
    ):
        """
        Initiate a transaction
        :param sort: the type of transaction. CREATE or CALL or DELEGATECALL
        :param address: the address of the account which owns the code that is executing.
        :param price: the price of gas in the transaction that originated this execution.
        :param data: the byte array that is the input data to this execution
        :param caller: the address of the account which caused the code to be executing. A 160-bit code used for identifying Accounts
        :param value: the value, in Wei, passed to this account as part of the same procedure as execution. One Ether is defined as being 10**18 Wei.
        :param bytecode: the byte array that is the machine code to be executed.
        :param gas: gas budget for this transaction.
        """
        assert self._pending_transaction is None, "Already started tx"
        self._pending_transaction = PendingTransaction(
            sort, address, price, data, caller, value, gas
        )

    def _constraint_to_accounts(self, address, include_zero=False, ty="both"):
        if ty not in ("both", "normal", "contract"):
            raise ValueError("Bad account type. It must be `normal`, `contract` or `both`")
        if ty == "both":
            accounts = self.accounts
        elif ty == "normal":
            accounts = self.normal_accounts
        else:
            assert ty == "contract"
            accounts = self.contract_accounts

        # Constraint it so it can range over all accounts + address0
        cond = True
        if accounts:
            cond = None
            if include_zero:
                cond = address == 0

            for known_account in accounts:
                if cond is None:
                    cond = address == known_account
                else:
                    cond = Operators.OR(address == known_account, cond)
        return cond

    def _pending_transaction_concretize_address(self):
        sort, address, price, data, caller, value, gas = self._pending_transaction
        if issymbolic(address):

            def set_address(state, solution):
                world = state.platform
                world._pending_transaction = sort, solution, price, data, caller, value, gas

            cond = self._constraint_to_accounts(address, ty="contract", include_zero=False)
            self.constraints.add(cond)
            raise Concretize(
                "Concretizing address on transaction",
                expression=address,
                setstate=set_address,
                policy="ALL",
            )

    def _pending_transaction_concretize_caller(self):
        sort, address, price, data, caller, value, gas = self._pending_transaction
        if issymbolic(caller):

            def set_caller(state, solution):
                world = state.platform
                world._pending_transaction = sort, address, price, data, solution, value, gas

            # Constrain it so it can range over all normal accounts
            cond = self._constraint_to_accounts(caller, ty="normal")
            self.constraints.add(cond)
            raise Concretize(
                "Concretizing caller on transaction",
                expression=caller,
                setstate=set_caller,
                policy="ALL",
            )

    def _process_pending_transaction(self):
        # Nothing to do here if no pending transactions
        if self._pending_transaction is None:
            return
        sort, address, price, data, caller, value, gas = self._pending_transaction

        if sort not in {"CALL", "CREATE", "DELEGATECALL", "CALLCODE"}:
            if sort == "STATICCALL":
                # TODO: Remove this once Issue #1168 is resolved
                raise EVMException(
                    f"The STATICCALL opcode is not yet supported; see https://github.com/trailofbits/manticore/issues/1168"
                )
            else:
                raise EVMException(f"Transaction type '{sort}' not supported")

        if self.depth > 0:
            assert price is None, "Price should not be used in internal transactions"
            price = self.tx_gasprice()

        if price is None:
            raise EVMException("Need to set a gas price on human tx")
        self._pending_transaction_concretize_address()
        self._pending_transaction_concretize_caller()
        if caller not in self.accounts:
            raise EVMException(
                f"Caller account {hex(caller)} does not exist; valid accounts: {list(map(hex, self.accounts))}"
            )

        if address not in self.accounts:
            # Creating an unaccessible account
            self.create_account(address=address)

        # Check depth
        failed = self.depth > 1024

        # Fork on enough funds
        if not failed:
            src_balance = self.get_balance(caller)
            enough_balance = Operators.UGE(src_balance, value)
            enough_balance_solutions = Z3Solver().get_all_values(self._constraints, enough_balance)

            if set(enough_balance_solutions) == {True, False}:
                raise Concretize(
                    "Forking on available funds",
                    expression=enough_balance,
                    setstate=lambda a, b: None,
                    policy="ALL",
                )
            failed = set(enough_balance_solutions) == {False}
        # processed
        self._pending_transaction = None
        # Here we have enough funds and room in the callstack
        # CALLCODE and  DELEGATECALL do not send funds
        if sort in ("CALL", "CREATE"):
            self.send_funds(caller, address, value)

        self._open_transaction(sort, address, price, data, caller, value, gas=gas)

        if failed:
            self._close_transaction("TXERROR", rollback=True)
        # Transaction to normal account
        elif sort in ("CALL", "DELEGATECALL", "CALLCODE") and not self.get_code(address):
            self._close_transaction("STOP")

    def dump(self, stream, state, mevm, message):
        from ..ethereum.manticore import calculate_coverage, flagged

        blockchain = state.platform
        last_tx = blockchain.last_transaction

        stream.write("Message: %s\n" % message)
        stream.write("Last exception: %s\n" % state.context.get("last_exception", "None"))

        if last_tx:
            at_runtime = last_tx.sort != "CREATE"
            address, offset, at_init = state.context["evm.trace"][-1]
            assert last_tx.result is not None or at_runtime != at_init

            # Last instruction if last tx was valid
            if str(state.context["last_exception"]) != "TXERROR":
                metadata = mevm.get_metadata(blockchain.last_transaction.address)
                if metadata is not None:
                    stream.write("Last instruction at contract %x offset %x\n" % (address, offset))
                    source_code_snippet = metadata.get_source_for(offset, at_runtime)
                    if source_code_snippet:
                        stream.write("    ".join(source_code_snippet.splitlines(True)))
                    stream.write("\n")

        # Accounts summary
        is_something_symbolic = False
        stream.write("%d accounts.\n" % len(blockchain.accounts))
        for account_address in blockchain.accounts:
            is_account_address_symbolic = issymbolic(account_address)
            account_address = state.solve_one(account_address)

            stream.write("* %s::\n" % mevm.account_name(account_address))
            stream.write(
                "Address: 0x%x %s\n" % (account_address, flagged(is_account_address_symbolic))
            )
            balance = blockchain.get_balance(account_address)
            is_balance_symbolic = issymbolic(balance)
            is_something_symbolic = is_something_symbolic or is_balance_symbolic
            balance = state.solve_one(balance)
            stream.write("Balance: %d %s\n" % (balance, flagged(is_balance_symbolic)))

            storage = blockchain.get_storage(account_address)
            stream.write("Storage: %s\n" % translate_to_smtlib(storage, use_bindings=True))

            all_used_indexes = []
            with state.constraints as temp_cs:
                index = temp_cs.new_bitvec(256)
                storage = blockchain.get_storage(account_address)
                temp_cs.add(storage.get(index) != 0)

                try:
                    while True:
                        a_index = Z3Solver().get_value(temp_cs, index)
                        all_used_indexes.append(a_index)

                        temp_cs.add(storage.get(a_index) != 0)
                        temp_cs.add(index != a_index)
                except Exception:
                    pass

            if all_used_indexes:
                stream.write("Storage:\n")
                for i in all_used_indexes:
                    value = storage.get(i)
                    is_storage_symbolic = issymbolic(value)
                    stream.write(
                        "storage[%x] = %x %s\n"
                        % (state.solve_one(i), state.solve_one(value), flagged(is_storage_symbolic))
                    )

            runtime_code = state.solve_one(blockchain.get_code(account_address))
            if runtime_code:
                stream.write("Code:\n")
                fcode = io.BytesIO(runtime_code)
                for chunk in iter(lambda: fcode.read(32), b""):
                    stream.write("\t%s\n" % binascii.hexlify(chunk))
                runtime_trace = set(
                    (
                        pc
                        for contract, pc, at_init in state.context["evm.trace"]
                        if address == contract and not at_init
                    )
                )
                stream.write(
                    "Coverage %d%% (on this state)\n"
                    % calculate_coverage(runtime_code, runtime_trace)
                )  # coverage % for address in this account/state
            stream.write("\n")
        return is_something_symbolic


_FILTER = "".join((len(repr(chr(x))) == 3) and chr(x) or "." for x in range(256))


def _hexdump(src, length=16):
    lines = []
    for c in range(0, len(src), length):
        chars = src[c : c + length]

        def p(x):
            if issymbolic(x):
                return "??"
            else:
                return "%02x" % x

        hex = " ".join(p(x) for x in chars)

        def p1(x):
            if issymbolic(x):
                return "."
            else:
                return "%s" % ((x <= 127 and _FILTER[x]) or ".")

        printable = "".join(p1(x) for x in chars)
        lines.append("%04x  %-*s  %s" % (c, length * 3, hex, printable))
    return lines
