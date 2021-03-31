"""Symbolic EVM implementation based on the yellow paper: http://gavwood.com/paper.pdf"""
import uuid
import binascii
import random
import io
import copy
import inspect
from functools import wraps
from typing import List, Set, Tuple, Union
from ..platforms.platform import *
from ..core.smtlib import (
    SelectedSolver,
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
    get_depth,
    issymbolic,
    get_taints,
    istainted,
    taint_with,
)
from ..core.state import Concretize, TerminateState
from ..utils.event import Eventful
from ..utils.helpers import printable_bytes
from ..utils import config
from ..core.smtlib.visitors import simplify
from ..exceptions import EthereumError
import pyevmasm as EVMAsm
import logging
from collections import namedtuple
import sha3
import rlp

logger = logging.getLogger(__name__)

# Gas behaviour configuration
# When gas is concrete the gas checks and calculation are pretty straight forward
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
DEFAULT_FORK = "istanbul"


def globalsha3(data):
    if issymbolic(data):
        return None
    return int(sha3.keccak_256(data).hexdigest(), 16)


def globalfakesha3(data):
    return None


consts.add(
    "oog",
    default="ignore",
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

consts.add(
    "txfail",
    default="optimistic",
    description=(
        "Default behavior for transaction failing because not enough funds."
        "optimistic: Assume there is always enough funds to pay for value and gas. Wont fork"
        "pessimistic: Assume the balance is never enough for paying fo a transaction. Wont fork"
        "both: Will fork for both options if possible."
    ),
)

consts.add(
    "calldata_max_offset",
    default=1024 * 1024,
    description="Max calldata offset to explore with. Iff offset or size in a calldata related instruction are symbolic it will be constrained to this constant",
)
consts.add(
    "calldata_max_size",
    default=-1,
    description="Max calldata size to explore in each CALLDATACOPY. Iff size in a calldata related instruction are symbolic it will be constrained to be less than this constant. -1 means free(only use when gas is being tracked)",
)
consts.add(
    "ignore_balance",
    default=False,
    description="Do not try to solve symbolic balances",
)


# Auxiliary constants and functions
TT256 = 2 ** 256
TT256M1 = 2 ** 256 - 1
MASK160 = 2 ** 160 - 1
TT255 = 2 ** 255
TOOHIGHMEM = 0x1000
DEFAULT_FORK = "istanbul"

# FIXME. We should just use a Transaction() for this
PendingTransaction = namedtuple(
    "PendingTransaction", ["type", "address", "price", "data", "caller", "value", "gas", "failed"]
)
EVMLog = namedtuple("EVMLog", ["address", "memlog", "topics"])
BlockHeader = namedtuple(
    "BlockHeader", ["blocknumber", "timestamp", "difficulty", "gaslimit", "coinbase"]
)


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
        "_used_gas",
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
        used_gas=None,
    ):
        self.sort = sort
        self.address = address
        self.price = price
        self.data = data
        self.caller = caller
        self.value = value
        self.depth = depth
        self.gas = gas
        self.set_result(result, return_data, used_gas)

    def concretize(self, state, constrain=False):
        """
        :param state: a manticore state
        :param bool constrain: If True, constrain expr to concretized value
        """
        all_elems = [
            self.caller,
            self.address,
            self.value,
            self.gas,
            self.data,
            self._return_data,
            self.used_gas,
        ]
        values = state.solve_one_n_batched(all_elems, constrain=constrain)
        conc_caller = values[0]
        conc_address = values[1]
        conc_value = values[2]
        conc_gas = values[3]
        conc_data = values[4]
        conc_return_data = values[5]
        conc_used_gas = values[6]

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
            return_data=conc_return_data,
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
            used_gas=self.used_gas,
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
        if len(tx_data) > 80:
            tx_data = tx_data.rstrip(conc_tx.data[-3:-1])

        stream.write(
            "Data: 0x{} {}\n".format(
                binascii.hexlify(tx_data).decode(), flagged(issymbolic(self.data))
            )
        )

        if self.return_data is not None:
            return_data = conc_tx.return_data

            stream.write(
                "Return_data: 0x{} {} {}\n".format(
                    binascii.hexlify(return_data).decode(),
                    f"({printable_bytes(return_data)})" if conc_tx.sort != "CREATE" else "",
                    flagged(issymbolic(self.return_data)),
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
                stream.write(",".join(map(repr, arguments)))
                stream.write(") -> %s %s\n" % (self.result, flagged(is_argument_symbolic)))

        if self.sort == "CALL":
            if metadata is not None:
                calldata = conc_tx.data
                is_calldata_symbolic = issymbolic(self.data)

                function_id = bytes(calldata[:4])  # hope there is enough data
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
        if sort not in {"CREATE", "CALL", "CALLCODE", "DELEGATECALL"}:
            raise EVMException(f"Invalid transaction type: {sort}")
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
            if self.sort == "CREATE":
                return self.address
            else:
                return 1
        else:
            assert self.result in {"TXERROR", "REVERT", "THROW"}
            return 0

    @property
    def used_gas(self):
        return self._used_gas

    def set_result(self, result, return_data=None, used_gas=None):
        if getattr(self, "result", None) is not None:
            raise EVMException("Transaction result already set")
        if not isinstance(used_gas, (int, BitVec, type(None))):
            raise EVMException("Invalid used gas in Transaction")
        if result not in {None, "TXERROR", "REVERT", "RETURN", "THROW", "STOP", "SELFDESTRUCT"}:
            raise EVMException("Invalid transaction result")
        if result in {"RETURN", "REVERT"}:
            if not isinstance(return_data, (bytes, bytearray, Array)):
                raise EVMException(
                    "Invalid transaction return_data type:", type(return_data).__name__
                )
        elif result in {"STOP", "THROW", "SELFDESTRUCT"}:
            if return_data is None:
                return_data = b""
            if not isinstance(return_data, (bytes, bytearray, Array)) or len(return_data) != 0:
                raise EVMException(
                    f"Invalid transaction return_data. Too much data ({len(return_data)}) for STOP, THROW or SELFDESTRUCT"
                )
        else:
            if return_data is not None:
                raise EVMException("Invalid transaction return_data")
        self._result = result
        self._return_data = return_data
        self._used_gas = used_gas

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
                self.used_gas,
            ),
        )

    def __str__(self):
        return "Transaction({:s}, from=0x{:x}, to=0x{:x}, value={!r}, depth={:d}, data={!r}, result={!r}, gas={!r} ..)".format(
            self.sort,
            self.caller,
            self.address,
            self.value,
            self.depth,
            self.data,
            self.result,
            self.gas,
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


class Throw(EndTx):
    def __init__(self):
        super().__init__("THROW")


class InvalidOpcode(Throw):
    """Trying to execute invalid opcode"""


class StackOverflow(Throw):
    """Attempted to push more than 1024 items"""

    pass


class StackUnderflow(Throw):
    """Attempted to pop from an empty stack"""

    pass


class NotEnoughGas(Throw):
    """Not enough gas for operation"""

    pass


class Stop(EndTx):
    """Program reached a STOP instruction"""

    def __init__(self):
        super().__init__("STOP")


class Return(EndTx):
    """Program reached a RETURN instruction"""

    def __init__(self, data=bytes()):
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
    r"""
    Make sure an EVM instruction has all of its arguments concretized according to
    provided policies.

    Example decoration:

        @concretized_args(size='ONE', address='')
        def LOG(self, address, size, \*topics):
        ...

    The above will make sure that the *size* parameter to LOG is Concretized when symbolic
    according to the 'ONE' policy and concretize *address* with the default policy.

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
                if not issymbolic(args[index]) or isinstance(args[index], Constant):
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
                        "the value might not be tracked properly (This may affect detectors)"
                    )
                logger.info(
                    f"Concretizing instruction {args[0].world.current_vm.instruction} argument {arg} by {policy}"
                )

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
        "evm_write_code",
        "decode_instruction",
        "on_unsound_symbolication",
        "solve",
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

            @wraps(self._pre)
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
        self,
        constraints,
        address,
        data,
        caller,
        value,
        bytecode,
        world=None,
        gas=None,
        fork=DEFAULT_FORK,
        **kwargs,
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
        self._need_check_jumpdest = False
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
            caller  # address of the account that is directly responsible for this execution
        )
        self.data = data
        self.value = value
        self._bytecode = bytecode
        self.suicides = set()
        self.logs = []
        # FIXME parse decode and mark invalid instructions
        # self.invalid = set()

        # Machine state
        self.evmfork = fork
        self._pc = 0
        self.stack = []
        # We maintain gas as a 512 bits internally to avoid overflows
        # it is shortened to 256 bits when it is used by the GAS instruction
        self._gas = Operators.ZEXTEND(gas, 512)
        self._world = world
        self._allocated = 0
        self._on_transaction = False  # for @transact
        self._checkpoint_data = None
        self._published_pre_instruction_events = False
        self._return_data = b""

        # Used calldata size
        self._used_calldata_size = 0
        self._valid_jmpdests = set()
        self._sha3 = {}
        self._refund = 0
        self._temp_call_gas = None
        self._failed = False

    def fail_if(self, failed):
        self._failed = Operators.OR(self._failed, failed)

    def is_failed(self):
        if isinstance(self._failed, bool):
            return self._failed

        self._failed = simplify(self._failed)
        if isinstance(self._failed, Constant):
            return self._failed.value

        def setstate(state, value):
            state.platform._failed = value

        raise Concretize(
            "Transaction failed", expression=self._failed, setstate=lambda a, b: None, policy="ALL"
        )

    @property
    def pc(self):
        return self._pc

    @pc.setter
    def pc(self, pc):
        self._pc = simplify(pc)

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
        return Operators.EXTRACT(self._gas, 0, 256)

    def __getstate__(self):
        state = super().__getstate__()
        state["sha3"] = self._sha3
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
        state["_valid_jumpdests"] = self._valid_jumpdests
        state["_need_check_jumpdest"] = self._need_check_jumpdest
        state["_return_data"] = self._return_data
        state["evmfork"] = self.evmfork
        state["_refund"] = self._refund
        state["_temp_call_gas"] = self._temp_call_gas
        state["_failed"] = self._failed
        return state

    def __setstate__(self, state):
        self._sha3 = state["sha3"]
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
        self._valid_jumpdests = state["_valid_jumpdests"]
        self._need_check_jumpdest = state["_need_check_jumpdest"]
        self._return_data = state["_return_data"]
        self.evmfork = state["evmfork"]
        self._refund = state["_refund"]
        self._temp_call_gas = state["_temp_call_gas"]
        self._failed = state["_failed"]
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
        address_c = Operators.UDIV(self.safe_add(address, size, 31), 32) * 32
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

    def _getcode(self, pc):
        bytecode = self.bytecode
        for pc_i in range(pc, len(bytecode)):
            yield simplify(bytecode[pc_i]).value
        while True:
            yield 0  # STOP opcode

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
            self._decoding_cache = {}
            _decoding_cache = self._decoding_cache

        pc = self.pc
        if isinstance(pc, Constant):
            pc = pc.value

        if pc in _decoding_cache:
            return _decoding_cache[pc]

        instruction = EVMAsm.disassemble_one(self._getcode(pc), pc=pc, fork=self.evmfork)
        _decoding_cache[pc] = instruction
        return instruction

    # auxiliary funcs
    def _throw(self):
        self._gas = 0
        raise InvalidOpcode()

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

        oog_condition = simplify(Operators.ULT(self._gas, fee))
        self.fail_if(oog_condition)

        self._gas = simplify(self._gas - fee)
        if isinstance(self._gas, Constant) and not self._gas.taint:
            self._gas = self._gas.value

    def check_oog(self):
        if consts.oog == "concrete":
            # Keep gas concrete and ogg checked at every instruction
            if issymbolic(self._gas):
                raise ConcretizeGas()
            if self.is_failed():
                raise NotEnoughGas()

        if consts.oog == "pedantic":
            # gas is faithfully accounted and ogg checked at every instruction
            if self.is_failed():
                raise NotEnoughGas()

        elif consts.oog == "complete":
            if self.instruction.is_terminator:
                # gas is faithfully accounted and ogg checked at every BB
                if self.is_failed():
                    raise NotEnoughGas()

        elif consts.oog == "optimistic":
            self.constraints.add(self._failed == False)
            if self.is_failed():
                raise NotEnoughGas()

        elif consts.oog == "pessimistic":
            # OOG soon. If it may NOT be enough gas we ignore the normal case.
            # A constraint is added to assert the gas is NOT enough and the other state is ignored.
            # explore only when there is enough gas if possible
            self.constraints.add(self._failed == True)
            if self.is_failed():
                raise NotEnoughGas()
        else:
            assert consts.oog == "ignore", "Wrong oog config variable"
            # do nothing. gas is not even changed
            return

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
                # self._publish("will_decode_instruction", self.pc)
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
            self.check_oog()

        return self._checkpoint_data

    def _rollback(self):
        """Revert the stack, gas, pc and memory allocation so it looks like before executing the instruction"""
        last_pc, last_gas, last_instruction, last_arguments, fee, allocated = self._checkpoint_data
        self._push_arguments(last_arguments)
        self._gas = last_gas
        self.pc = last_pc
        self._allocated = allocated
        self._checkpoint_data = None

    def _set_check_jmpdest(self, flag=True):
        """
        Next instruction must be a JUMPDEST iff `flag` holds.

        Note that at this point `flag` can be the conditional from a JUMPI
        instruction hence potentially a symbolic value.
        """
        self._need_check_jumpdest = flag

    def _check_jmpdest(self):
        """
        If the previous instruction was a JUMP/JUMPI and the conditional was
        True, this checks that the current instruction must be a JUMPDEST.

        Here, if symbolic, the conditional `self._need_check_jumpdest` would be
        already constrained to a single concrete value.
        """
        # If pc is already pointing to a JUMPDEST thre is no need to check.
        pc = self.pc.value if isinstance(self.pc, Constant) else self.pc
        if pc in self._valid_jumpdests:
            self._need_check_jumpdest = False
            return

        should_check_jumpdest = simplify(self._need_check_jumpdest)
        if isinstance(should_check_jumpdest, Constant):
            should_check_jumpdest = should_check_jumpdest.value
        elif issymbolic(should_check_jumpdest):
            self._publish("will_solve", self.constraints, should_check_jumpdest, "get_all_values")
            should_check_jumpdest_solutions = SelectedSolver.instance().get_all_values(
                self.constraints, should_check_jumpdest
            )
            self._publish(
                "did_solve",
                self.constraints,
                should_check_jumpdest,
                "get_all_values",
                should_check_jumpdest_solutions,
            )
            if len(should_check_jumpdest_solutions) != 1:
                raise EthereumError("Conditional not concretized at JMPDEST check")
            should_check_jumpdest = should_check_jumpdest_solutions[0]

        # If it can be solved only to False just set it False. If it can be solved
        # only to True, process it and also set it to False
        self._need_check_jumpdest = False

        if should_check_jumpdest:
            if pc not in self._valid_jumpdests:
                self._throw()

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
                    state.platform.current_vm.pc = BitVecConstant(
                        size=256, value=value, taint=taints
                    )
                else:
                    state.platform.current_vm.pc = value

            raise Concretize("Symbolic PC", expression=expression, setstate=setstate, policy="ALL")
        try:
            self._check_jmpdest()
            last_pc, last_gas, instruction, arguments, fee, allocated = self._checkpoint()
            result = self._handler(*arguments)
            self._advance(result)
        except ConcretizeGas as ex:

            def setstate(state, value):
                state.platform.current._gas = value

            raise Concretize(
                "Concretize gas", expression=self._gas, setstate=setstate, policy="MINMAX"
            )
        except ConcretizeFee as ex:

            def setstate(state, value):
                current_vm = state.platform.current_vm
                (
                    _pc,
                    _old_gas,
                    _instruction,
                    _arguments,
                    _fee,
                    _allocated,
                ) = current_vm._checkpoint_data
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
                expression=self._checkpoint_data[4],
                setstate=setstate,
                policy=ex.policy,
            )
        except ConcretizeArgument as ex:
            pos = ex.pos - 1

            def setstate(state, value):
                current_vm = state.platform.current_vm
                (
                    _pc,
                    _old_gas,
                    _instruction,
                    _arguments,
                    _fee,
                    _allocated,
                ) = current_vm._checkpoint_data
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
        except NotEnoughGas:
            # If tried to pay gas and failed then consume all of it
            self._gas = 0
            raise
        except StartTx:
            raise
        except EndTx as ex:
            if isinstance(ex, Throw):
                self._gas = 0
            self._advance(exception=True)
            raise

    def read_buffer(self, offset, size):
        if issymbolic(size) and not isinstance(size, Constant):
            raise EVMException("Symbolic size not supported")
        if isinstance(size, Constant):
            size = size.value
        if size == 0:
            return b""
        self._allocate(offset, size)
        data = self.memory[offset : offset + size]
        return ArrayProxy(array=data)

    def write_buffer(self, offset, data):
        self._allocate(offset, len(data))
        for i, c in enumerate(data):
            self._store(offset + i, Operators.ORD(c))

    def _load(self, offset, size=1):
        value = self.memory.read_BE(offset, size)
        value = simplify(value)
        if isinstance(value, Constant) and not value.taint:
            value = value.value
        self._publish("did_evm_read_memory", offset, value, size)
        return value

    def _store(self, offset, value, size=1):
        """Stores value in memory as a big endian"""
        self.memory.write_BE(offset, value, size)
        self._publish("did_evm_write_memory", offset, value, size)

    def safe_add(self, a, b, *args):
        a = Operators.ZEXTEND(a, 512)
        b = Operators.ZEXTEND(b, 512)
        result = a + b
        if len(args) > 0:
            result = self.safe_add(result, *args)
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
        self._throw()

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
            result = Operators.EXTRACT(self.safe_add(a, b) % Operators.ZEXTEND(c, 512), 0, 256)
            result = Operators.ITEBV(256, c == 0, 0, result)
        except ZeroDivisionError:
            result = 0
        return result

    def MULMOD(self, a, b, c):
        """Modulo addition operation"""
        try:
            result = Operators.EXTRACT(self.safe_mul(a, b) % Operators.ZEXTEND(c, 512), 0, 256)
            result = Operators.ITEBV(256, c == 0, 0, result)
        except ZeroDivisionError:
            result = 0
        return result

    def EXP_gas(self, base, exponent):
        """Calculate extra gas fee"""
        EXP_SUPPLEMENTAL_GAS = 50  # cost of EXP exponent per byte

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

    def SHL(self, a, b):
        """Shift Left operation"""
        return b << a

    def SHR(self, a, b):
        """Logical Shift Right operation"""
        return b >> a

    def SAR(self, a, b):
        """Arithmetic Shift Right operation"""
        return Operators.SAR(256, b, a)

    def SHA3_gas(self, start, size):
        GSHA3WORD = 6  # Cost of SHA3 per word
        sha3fee = self.safe_mul(GSHA3WORD, ceil32(size) // 32)
        memfee = self._get_memfee(start, size)
        return self.safe_add(sha3fee, memfee)

    @concretized_args(size="ALL")
    def SHA3(self, start, size):
        """Compute Keccak-256 hash
        If the size is symbolic the potential solutions will be sampled as
        defined by the default policy and the analysis will be forked.
        The `size` can be considered concrete in this handler.

        """
        data = self.read_buffer(start, size)
        if consts.sha3 is consts.sha3.fake:
            func = globalfakesha3
        else:
            func = globalsha3
        return self.world.symbolic_function(func, data)

    ############################################################################
    # Environmental Information
    def ADDRESS(self):
        """Get address of currently executing account"""
        return self.address

    def BALANCE_gas(self, account):
        return 700  # BALANCE_SUPPLEMENTAL_GAS

    def BALANCE(self, account):
        """Get balance of the given account"""
        return self.world.get_balance(account)

    def SELFBALANCE(self):
        return self.world.get_balance(self.address)

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
        # calldata_overflow = const.calldata_overflow
        calldata_overflow = None  # 32
        if calldata_overflow is not None:
            self.constraints.add(self.safe_add(offset, 32) <= len(self.data) + calldata_overflow)

        self._use_calldata(offset, 32)

        data_length = len(self.data)
        bytes = []
        for i in range(32):
            try:
                c = simplify(
                    Operators.ITEBV(
                        8,
                        Operators.ULT(self.safe_add(offset, i), data_length),
                        self.data[offset + i],
                        0,
                    )
                )
            except IndexError:
                # offset + i is concrete and outside data
                c = 0
            bytes.append(c)
        return Operators.CONCAT(256, *bytes)

    def _use_calldata(self, offset, size):
        """To improve reporting we maintain how much of the calldata is actually
        used. CALLDATACOPY and CALLDATA LOAD update this limit accordingly"""
        self._used_calldata_size = Operators.ITEBV(
            256, size != 0, self._used_calldata_size + offset + size, self._used_calldata_size
        )

    def CALLDATASIZE(self):
        """Get size of input data in current environment"""
        return len(self.data)

    def CALLDATACOPY_gas(self, mem_offset, data_offset, size):
        GCOPY = 3  # cost to copy one 32 byte word
        copyfee = self.safe_mul(GCOPY, self.safe_add(size, 31) // 32)
        memfee = self._get_memfee(mem_offset, size)
        return self.safe_add(copyfee, memfee)

    # @concretized_args(size="SAMPLED")
    def CALLDATACOPY(self, mem_offset, data_offset, size):
        """Copy input data in current environment to memory"""
        # calldata_overflow = const.calldata_overflow
        # calldata_underflow = const.calldata_underflow
        calldata_overflow = None  # 32
        if calldata_overflow is not None:
            self.constraints.add(
                Operators.ULT(self.safe_add(data_offset, size), len(self.data) + calldata_overflow)
            )

        self._use_calldata(data_offset, size)
        self._allocate(mem_offset, size)

        if consts.oog == "complete":
            # gas reduced #??
            cond = Operators.ULT(self.gas, self._checkpoint_data[1])
            self._publish("will_solve", self.constraints, cond, "can_be_true")
            enough_gas = SelectedSolver.instance().can_be_true(self.constraints, cond)
            self._publish("did_solve", self.constraints, cond, "can_be_true", enough_gas)
            if not enough_gas:
                raise NotEnoughGas()
            self.constraints.add(cond)

        if consts.calldata_max_size >= 0:
            self.constraints.add(Operators.ULE(size, consts.calldata_max_size))

        max_size = size
        if issymbolic(max_size):
            self._publish("will_solve", self.constraints, size, "max")
            max_size = SelectedSolver.instance().max(self.constraints, size)
            self._publish("did_solve", self.constraints, size, "max", max_size)

        if calldata_overflow is not None:
            cap = len(self.data) + calldata_overflow
            if max_size > cap:
                logger.info(f"Constraining CALLDATACOPY size to {cap}")
                max_size = cap
                self.constraints.add(Operators.ULE(size, cap))

        for i in range(max_size):
            try:
                c1 = Operators.ITEBV(
                    8,
                    Operators.ULT(self.safe_add(data_offset, i), len(self.data)),
                    Operators.ORD(self.data[data_offset + i]),
                    0,
                )

            except IndexError:
                # data_offset + i is concrete and outside data
                c1 = 0

            c = simplify(Operators.ITEBV(8, i < size, c1, self.memory[mem_offset + i]))
            if not issymbolic(c) or get_depth(c) < 3:
                x = c
            else:
                # if te expression is deep enough lets replace it by a binding
                x = self.constraints.new_bitvec(8, name="temp{}".format(uuid.uuid1()))
                self.constraints.add(x == c)
            self._store(mem_offset + i, x)

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
            self._publish("will_solve", self.constraints, size, "max")
            max_size = SelectedSolver.instance().max(self.constraints, size)
            self._publish("did_solve", self.constraints, size, "max", max_size)
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
        self._publish("did_evm_read_code", self.address, code_offset, size)

    def GASPRICE(self):
        """Get price of gas in current environment"""
        return self.world.tx_gasprice()

    @concretized_args(account="ACCOUNTS")
    def EXTCODESIZE(self, account):
        """Get size of an account's code"""
        return len(self.world.get_code(account))

    @concretized_args(account="ACCOUNTS")
    def EXTCODEHASH(self, account):
        """Get hash of code"""
        bytecode = self.world.get_code(account)
        return globalsha3(bytecode)

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
            self._publish("did_evm_read_code", address, offset, size)

    def RETURNDATACOPY_gas(self, mem_offset, return_offset, size):
        return self._get_memfee(mem_offset, size)

    def RETURNDATACOPY(self, mem_offset, return_offset, size):
        return_data = self._return_data

        self._allocate(mem_offset, size)
        for i in range(size):
            if return_offset + i < len(return_data):
                self._store(mem_offset + i, return_data[return_offset + i])
            else:
                self._store(mem_offset + i, 0)

    def RETURNDATASIZE(self):
        return len(self._return_data)

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

    def CHAINID(self):
        """Get current chainid."""
        #  1:= Ethereum Mainnet - https://chainid.network/
        return 1

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
            value = taint_with(value, *get_taints(self.pc))
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
        SSSTORESENTRYGAS = (
            2300  # Minimum gas required to be present for an SSTORE call, not consumed
        )
        SSTORENOOP = 800  # Once per SSTORE operation if the value doesn't change.
        SSTOREDIRTYGAS = 800  # Once per SSTORE operation if a dirty value is changed.
        SSTOREINITGAS = 20000  # Once per SSTORE operation from clean zero to non-zero
        SstoreInitRefund = (
            19200  # Once per SSTORE operation for resetting to the original zero value
        )
        SSTORECLEANGAS = 5000  # Once per SSTORE operation from clean non-zero to something else
        SstoreCleanRefund = (
            4200  # Once per SSTORE operation for resetting to the original non-zero value
        )
        SstoreClearRefund = (
            15000  # Once per SSTORE operation for clearing an originally existing storage slot
        )

        self.fail_if(Operators.ULT(self.gas, SSSTORESENTRYGAS))

        # Get the storage from the snapshot took before this call
        try:
            original_value = self.world._callstack[-1][-2].get(offset, 0)
        except IndexError:
            original_value = 0

        current_value = self.world.get_storage_data(storage_address, offset)

        def ITE(*args):
            return Operators.ITEBV(512, *args)

        def AND(*args):
            return Operators.AND(*args)

        gascost = ITE(
            current_value == value,
            SSTORENOOP,
            ITE(
                original_value == current_value,
                ITE(original_value == 0, SSTOREINITGAS, SSTORECLEANGAS),
                SSTOREDIRTYGAS,
            ),
        )
        refund = 0
        refund += ITE(
            AND(
                current_value != value,
                original_value == current_value,
                original_value != 0,
                value == 0,
            ),
            SstoreClearRefund,
            0,
        )
        refund += ITE(
            AND(
                current_value != value,
                original_value != current_value,
                original_value != 0,
                current_value == 0,
            ),
            -SstoreClearRefund,
            0,
        )
        refund += ITE(
            AND(
                current_value != value,
                original_value != current_value,
                original_value != 0,
                current_value != 0,
                value == 0,
            ),
            SstoreClearRefund,
            0,
        )

        refund += ITE(
            AND(
                current_value != value,
                original_value != current_value,
                original_value == value,
                original_value == 0,
            ),
            SstoreInitRefund,
            0,
        )
        refund += ITE(
            AND(
                current_value != value,
                original_value != current_value,
                original_value == value,
                original_value != 0,
            ),
            SstoreCleanRefund,
            0,
        )
        self._refund += simplify(refund)
        return gascost

    def SSTORE(self, offset, value):
        """Save word to storage"""
        storage_address = self.address
        self._publish("will_evm_write_storage", storage_address, offset, value)

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
        # TODO(feliam) If dest is Constant we do not need to 3 queries. There would
        # be only 2 options

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
        return self.gas

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
        self._consume(self.safe_mul(size, GLOGBYTE))
        memlog = self.read_buffer(address, size)
        self.world.log(self.address, topics, memlog)

    ############################################################################
    # System operations
    def CREATE_gas(self, value, offset, size):
        return self._get_memfee(offset, size)

    @transact
    def CREATE(self, value, offset, size):
        """Create a new account with associated code"""
        data = self.read_buffer(offset, size)
        self.world.start_transaction(
            "CREATE", None, data=data, caller=self.address, value=value, gas=self.gas * 63 // 64
        )
        raise StartTx()

    @CREATE.pos  # type: ignore
    def CREATE(self, value, offset, size):
        """Create a new account with associated code"""
        tx = self.world.last_transaction  # At this point last and current tx are the same.
        return tx.return_value

    def CALL_gas(self, wanted_gas, address, value, in_offset, in_size, out_offset, out_size):
        """ Dynamic gas for CALL instruction. _arguably turing complete in itself_   """
        GCALLVALUE = 9000
        GCALLNEW = 25000
        wanted_gas = Operators.ZEXTEND(wanted_gas, 512)
        fee = Operators.ITEBV(512, value == 0, 0, GCALLVALUE)
        fee += Operators.ITEBV(
            512, Operators.OR(self.world.account_exists(address), value == 0), 0, GCALLNEW
        )
        fee += self._get_memfee(in_offset, in_size)

        exception = False
        available_gas = self._gas
        available_gas -= fee

        exception = Operators.OR(
            Operators.UGT(fee, self._gas),
            Operators.ULT(self.safe_mul(available_gas, 63), available_gas),
        )
        available_gas *= 63
        available_gas //= 64

        temp_call_gas = Operators.ITEBV(
            512, Operators.UGT(available_gas, wanted_gas), wanted_gas, available_gas
        )
        self._temp_call_gas = temp_call_gas
        return temp_call_gas + fee

    @transact
    @concretized_args(address="ACCOUNTS", in_offset="SAMPLED", in_size="SAMPLED")
    def CALL(self, gas, address, value, in_offset, in_size, out_offset, out_size):
        """Message-call into an account"""
        self.world.start_transaction(
            "CALL",
            address,
            data=self.read_buffer(in_offset, in_size),
            caller=self.address,
            value=value,
            gas=self._temp_call_gas + Operators.ITEBV(512, value != 0, 2300, 0),
        )
        raise StartTx()

    def __pos_call(self, out_offset, out_size):
        data = self._return_data
        data_size = len(data)
        size = Operators.ITEBV(256, Operators.ULT(out_size, data_size), out_size, data_size)
        self.write_buffer(out_offset, data[:size])
        self._get_memfee(out_offset, size)
        return self.world.transactions[-1].return_value

    @CALL.pos  # type: ignore
    def CALL(self, gas, address, value, in_offset, in_size, out_offset, out_size):
        return self.__pos_call(out_offset, out_size)

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

    @CALLCODE.pos  # type: ignore
    def CALLCODE(self, gas, address, value, in_offset, in_size, out_offset, out_size):
        return self.__pos_call(out_offset, out_size)

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

    @DELEGATECALL.pos  # type: ignore
    def DELEGATECALL(self, gas, address, in_offset, in_size, out_offset, out_size):
        return self.__pos_call(out_offset, out_size)

    def STATICCALL_gas(self, gas, address, in_offset, in_size, out_offset, out_size):
        return self._get_memfee(in_offset, in_size)

    @transact
    @concretized_args(in_offset="SAMPLED", in_size="SAMPLED")
    def STATICCALL(self, gas, address, in_offset, in_size, out_offset, out_size):
        """Message-call into an account"""
        self.world.start_transaction(
            "CALL",
            address,
            data=self.read_buffer(in_offset, in_size),
            caller=self.address,
            value=0,
            gas=gas,
        )
        raise StartTx()

    @STATICCALL.pos  # type: ignore
    def STATICCALL(self, gas, address, in_offset, in_size, out_offset, out_size):
        return self.__pos_call(out_offset, out_size)

    def REVERT_gas(self, offset, size):
        return self._get_memfee(offset, size)

    def REVERT(self, offset, size):
        data = self.read_buffer(offset, size)
        # FIXME return remaining gas
        raise EndTx("REVERT", data)

    def THROW(self):
        # revert balance on CALL fail
        raise EndTx("THROW")

    def SELFDESTRUCT_gas(self, recipient):
        CreateBySelfdestructGas = 25000
        SelfdestructRefundGas = 24000
        fee = 0
        if not self.world.account_exists(recipient) and self.world.get_balance(self.address) != 0:
            fee += CreateBySelfdestructGas

        if self.address not in self.world._deleted_accounts:
            self._refund += SelfdestructRefundGas

        return fee

    @concretized_args(recipient="ACCOUNTS")
    def SELFDESTRUCT(self, recipient):
        """Halt execution and register account for later deletion"""
        # This may create a user account
        recipient = Operators.EXTRACT(recipient, 0, 160)
        address = self.address

        if recipient not in self.world:
            self.world.create_account(address=recipient)

        self.world.send_funds(address, recipient, self.world.get_balance(address))
        self.world.delete_account(address)

        raise EndTx("SELFDESTRUCT")

    def __str__(self):
        m = []
        for offset in range(128):
            # c = simplify(self.memory[offset])
            c = self.memory[offset]
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
            argname = args.get(sp, "")
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
            # gas = simplify(gas)
            result.append(f"Gas: {translate_to_smtlib(gas)[:20]} {gas.taint}")
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
        "evm_write_code",
        "decode_instruction",
        "execute_instruction",
        "open_transaction",
        "close_transaction",
        "symbolic_function",
        "solve",
    }

    def __init__(self, constraints, fork=DEFAULT_FORK, **kwargs):
        super().__init__(path="NOPATH", **kwargs)
        self._world_state = {}
        self._constraints = constraints
        self._callstack: List[
            Tuple[Transaction, List[EVMLog], Set[int], Union[bytearray, ArrayProxy], EVM]
        ] = []
        self._deleted_accounts: Set[int] = set()
        self._logs: List[EVMLog] = list()
        self._pending_transaction = None
        self._transactions: List[Transaction] = list()
        self._fork = fork
        self._block_header = None
        self.start_block()

    def __getstate__(self):
        state = super().__getstate__()
        state["_pending_transaction"] = self._pending_transaction
        state["_logs"] = self._logs
        state["_world_state"] = self._world_state
        state["_constraints"] = self._constraints
        state["_callstack"] = self._callstack
        state["_deleted_accounts"] = self._deleted_accounts
        state["_transactions"] = self._transactions
        state["_fork"] = self._fork
        state["_block_header"] = self._block_header

        return state

    def __setstate__(self, state):
        super().__setstate__(state)
        self._constraints = state["_constraints"]
        self._pending_transaction = state["_pending_transaction"]
        self._world_state = state["_world_state"]
        self._deleted_accounts = state["_deleted_accounts"]
        self._logs = state["_logs"]
        self._callstack = state["_callstack"]
        self._transactions = state["_transactions"]
        self._fork = state["_fork"]
        self._block_header = state["_block_header"]

        for _, _, _, _, vm in self._callstack:
            self.forward_events_from(vm)

    def try_simplify_to_constant(self, data):
        concrete_data = bytearray()
        # for c in data:
        for index in range(len(data)):
            c = data[index]
            simplified = simplify(c)

            if isinstance(simplified, Constant):
                concrete_data.append(simplified.value)
            else:
                # simplify by solving. probably means that we need to improve simplification
                self._publish("will_solve", self.constraints, simplified, "get_all_values")
                solutions = SelectedSolver.instance().get_all_values(
                    self.constraints, simplified, 2, silent=True
                )
                self._publish(
                    "did_solve", self.constraints, simplified, "get_all_values", solutions
                )
                if len(solutions) != 1:
                    break
                concrete_data.append(solutions[0])
        else:
            data = bytes(concrete_data)
        return data

    def symbolic_function(self, func, data):
        """
        Get an unsound symbolication for function `func`

        """
        data = self.try_simplify_to_constant(data)
        try:
            result = []
            self._publish(
                "on_symbolic_function", func, data, result
            )  # This updates the local copy of result

            return result[0]
        except Exception as e:
            logger.info("Error! %r", e)
            self._publish("will_solve", self.constraints, data, "get_value")
            data_c = SelectedSolver.instance().get_value(self.constraints, data)
            self._publish("did_solve", self.constraints, data, "get_value", data_c)
            return int(sha3.keccak_256(data_c).hexdigest(), 16)

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
        return (
            "WORLD:"
            + str(self._world_state)
            + "\n"
            + str(list((map(str, self.transactions))))
            + str(self.logs)
        )

    @property
    def logs(self):
        return self._logs

    @property
    def constraints(self):
        return self._constraints

    @constraints.setter
    def constraints(self, constraints):
        self._constraints = constraints
        if self.current_vm:
            self.current_vm.constraints = constraints

    @property
    def evmfork(self):
        return self._fork

    def _transaction_fee(self, sort, address, price, bytecode_or_data, caller, value):
        GTXCREATE = (
            32000  # Paid by all contract creating transactions after the Homestead transition.
        )
        GTXDATAZERO = 4  # Paid for every zero byte of data or code for a transaction.
        GTXDATANONZERO = 16  # Paid for every non - zero byte of data or code for a transaction.
        GTRANSACTION = 21000  # Paid for every transaction
        if sort == "CREATE":
            tx_fee = GTXCREATE
        else:
            tx_fee = GTRANSACTION  # Simple transaction fee

        zerocount = 0
        nonzerocount = 0
        if isinstance(bytecode_or_data, (Array, ArrayProxy)):
            # if nothing was written we can assume all elements are default to zero
            if len(bytecode_or_data.written) == 0:
                zerocount = len(bytecode_or_data)
        else:
            for index in range(len(bytecode_or_data)):
                try:
                    c = bytecode_or_data.get(index, 0)
                except AttributeError:
                    c = bytecode_or_data[index]

                zerocount += Operators.ITEBV(256, c == 0, 1, 0)
                nonzerocount += Operators.ITEBV(256, c == 0, 0, 1)

        tx_fee += zerocount * GTXDATAZERO
        tx_fee += nonzerocount * GTXDATANONZERO
        return simplify(tx_fee)

    def _make_vm_for_tx(self, tx):
        if tx.sort == "CREATE":
            bytecode = tx.data
            data = bytes()
        else:
            bytecode = self.get_code(tx.address)
            data = tx.data

        if tx.sort == "DELEGATECALL":
            # So at a DELEGATECALL the environment should look exactly the same as the original tx
            # This means caller, value and address are the same as prev tx
            assert tx.value == 0
            address = self.current_transaction.address
            caller = self.current_transaction.caller
            value = self.current_transaction.value
        else:
            address = tx.address
            caller = tx.caller
            value = tx.value

        gas = tx.gas

        vm = EVM(self._constraints, address, data, caller, value, bytecode, world=self, gas=gas)
        if self.depth == 0:
            # Only at human level we need to debit the tx_fee from the gas
            # In case of an internal tx the CALL-like instruction will
            # take the fee by itself
            tx_fee = self._transaction_fee(
                tx.sort, tx.address, tx.price, tx.data, tx.caller, tx.value
            )
            vm._consume(tx_fee)
        return vm

    def _open_transaction(self, sort, address, price, bytecode_or_data, caller, value, gas=None):
        """
        This try to opens a transaction.

        :param sort: CREATE, CALL, CALLCODE, STATICCALL, DELEGATECALL
        :param address: the destination address
        :param price: the gas price. Used at human transactions
        :param bytecode_or_data: the calldata or bytecode in creates
        :param caller: the caller account
        :param value: wei to transfer
        :param gas: gas budget
        :return: True if the transaction got accepted (enough balance to pay for stuff)
        """
        # sort
        if sort not in {"CALL", "CREATE", "DELEGATECALL", "CALLCODE", "STATICCALL"}:
            raise EVMException(f"Transaction type '{sort}' not supported")

        if caller not in self.accounts:
            logger.info("Caller not in account")
            raise EVMException(
                f"Caller account {hex(caller)} does not exist; valid accounts: {list(map(hex, self.accounts))}"
            )

        if sort == "CREATE":
            expected_address = self.new_address(sender=caller)
            if address is None:
                address = expected_address
            if address != expected_address:
                raise EthereumError(
                    f"Error: contract created from address {hex(caller)} with nonce {self.get_nonce(caller)} was expected to be at address {hex(expected_address)}, but create_contract was called with address={hex(address)}"
                )

        if address not in self.accounts:
            logger.info("Address does not exists creating it.")
            # Creating an unaccessible account
            self.create_account(address=address, nonce=int(sort != "CREATE"))

        tx = Transaction(
            sort, address, price, bytecode_or_data, caller, value, depth=self.depth, gas=gas
        )
        self._publish("will_open_transaction", tx)
        # Send the tx funds (We know there are enough at this point)
        if self.depth == 0:
            # Debit full gas budget in advance
            aux_price = Operators.ZEXTEND(tx.price, 512)
            aux_gas = Operators.ZEXTEND(tx.gas, 512)
            self.sub_from_balance(caller, aux_price * aux_gas)
        self.send_funds(tx.caller, tx.address, tx.value)

        if tx.address not in self.accounts:
            self.create_account(tx.address)

        # If not a human tx, reset returndata
        # https://github.com/ethereum/EIPs/blob/master/EIPS/eip-211.md
        if self.current_vm:
            self.current_vm._return_data = b""

        vm = self._make_vm_for_tx(tx)

        self._callstack.append(
            (tx, self.logs, self.deleted_accounts, copy.copy(self.get_storage(address)), vm)
        )
        self.forward_events_from(vm)
        self._publish("did_open_transaction", tx)
        return True

    def _close_transaction(self, result, data=None, rollback=False):
        self._publish("will_close_transaction", self._callstack[-1][0])
        tx, logs, deleted_accounts, account_storage, vm = self._callstack.pop()
        assert self.constraints == vm.constraints
        # Keep constraints gathered in the last vm
        self.constraints = vm.constraints

        # https://github.com/ethereum/EIPs/blob/master/EIPS/eip-211.md
        if data is not None and self.current_vm is not None:
            self.current_vm._return_data = data
        if rollback:
            self._set_storage(vm.address, account_storage)
            self._logs = logs
            # Return the transaction value
            self.send_funds(tx.address, tx.caller, tx.value)
        else:
            self._deleted_accounts = deleted_accounts
        self.increase_nonce(tx.caller)

        if result in {"THROW"}:
            unused_gas = 0
            refund = 0
        else:
            unused_gas = vm._gas
            refund = vm._refund

        used_gas = Operators.ZEXTEND(tx.gas, 512) - unused_gas
        refund = Operators.ITEBV(512, Operators.UGE(refund, used_gas // 2), used_gas // 2, refund)

        if tx.is_human:
            for deleted_account in self._deleted_accounts:
                if deleted_account in self._world_state:
                    del self._world_state[deleted_account]
            unused_fee = unused_gas * tx.price
            used_fee = used_gas * tx.price
            self.add_to_balance(tx.caller, unused_fee)
            self.add_to_balance(tx.caller, refund * tx.price)
            if self.block_coinbase() in self:
                self.add_to_balance(self.block_coinbase(), used_fee - refund * tx.price)
            else:
                logger.info(
                    "Coinbase not set. Throwing %r weis for the gas", used_fee - refund * tx.price
                )
        else:
            # if not rollback:
            # Refund unused gas to caller if
            self.current_vm._gas += unused_gas
            self.current_vm._refund += refund
        if tx.sort == "CREATE":
            if result in ("RETURN", "STOP"):
                # vm.consume(len(tx.return_data) * GCREATEDATAGAS)
                self.set_code(tx.address, data)
            else:
                self.delete_account(tx.address)

        tx.set_result(result, data, used_gas - refund)
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
        return tuple(self._transactions)

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
        else:
            ret = self._world_state[address]["nonce"]
        return ret

    def increase_nonce(self, address):
        new_nonce = self.get_nonce(address) + 1
        self._world_state[address]["nonce"] = new_nonce
        return new_nonce

    def set_balance(self, address, value):
        if isinstance(value, BitVec):
            value = Operators.ZEXTEND(value, 512)
        self._world_state[int(address)]["balance"] = value

    def get_balance(self, address):
        if address not in self._world_state:
            return 0
        return Operators.EXTRACT(self._world_state[address]["balance"], 0, 256)

    def account_exists(self, address):
        if address not in self._world_state:
            return False  # accounts default to nonexistent
        return (
            self.has_code(address)
            or Operators.UGT(self.get_nonce(address), 0)
            or Operators.UGT(self.get_balance(address), 0)
        )

    def add_to_balance(self, address, value):
        if isinstance(value, BitVec):
            value = Operators.ZEXTEND(value, 512)
        self._world_state[address]["balance"] += value

    def sub_from_balance(self, address, value):
        if isinstance(value, BitVec):
            value = Operators.ZEXTEND(value, 512)
        self._world_state[address]["balance"] -= value

    def send_funds(self, sender, recipient, value):
        if isinstance(value, BitVec):
            value = Operators.ZEXTEND(value, 512)
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

    def log(self, address, topics, data):
        self._logs.append(EVMLog(address, data, topics))
        logger.info("LOG %r %r", data, topics)

    def log_storage(self, addr):
        pass

    def add_refund(self, value):
        self._refund += value

    def sub_refund(self, value):
        self._refund -= value

    def block_prevhash(self):
        return 0

    # Block header related
    def start_block(
        self,
        blocknumber=4370000,
        timestamp=1524785992,
        difficulty=0x200,
        gaslimit=0x7FFFFFFF,
        coinbase=0,
    ):
        if coinbase not in self.accounts and coinbase != 0:
            logger.info("Coinbase account does not exists")
            self.create_account(coinbase)

        self._block_header = BlockHeader(blocknumber, timestamp, difficulty, gaslimit, coinbase)

    def end_block(self, block_reward=None):
        coinbase = self.block_coinbase()
        if coinbase not in self:
            raise EVMException("Coinbase not set")

        if block_reward is None:
            block_reward = 2000000000000000000  # 2 eth
        self.add_to_balance(self.block_coinbase(), block_reward)
        # self._block_header = None

    def block_coinbase(self):
        return self._block_header.coinbase

    def block_timestamp(self):
        return self._block_header.timestamp

    def block_number(self):
        return self._block_header.blocknumber

    def block_difficulty(self):
        return self._block_header.difficulty

    def block_gaslimit(self):
        return self._block_header.gaslimit

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
            nonce = 1 if len(code) > 0 else 0

        if isinstance(balance, BitVec):
            balance = Operators.ZEXTEND(balance, 512)

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
        Initiates a CREATE a contract account.
        Sends a transaction to initialize the contract.
        Do a world.run() after this to explore all _possible_ outputs

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
        self.start_transaction(
            "CREATE", address, price=price, data=init, caller=caller, value=balance, gas=gas
        )
        return address

    def transaction(self, address, price=0, data="", caller=None, value=0, gas=2300):
        """Initiates a CALL transaction on current state.
        Do a world.run() after this to explore all _possible_ outputs
        """
        self.start_transaction(
            "CALL", address, price=price, data=data, caller=caller, value=value, gas=gas
        )

    def start_transaction(
        self, sort, address, *, price=None, data=None, caller=None, value=0, gas=2300
    ):
        """
        Initiate a transaction.

        :param sort: the type of transaction. CREATE or CALL or DELEGATECALL
        :param address: the address of the account which owns the code that is executing.
        :param price: the price of gas in the transaction that originated this execution.
        :param data: the byte array that is the input data to this execution
        :param caller: the address of the account which caused the code to be executing. A 160-bit code used for identifying Accounts
        :param value: the value, in Wei, passed to this account as part of the same procedure as execution. One Ether is defined as being 10**18 Wei.
        :param bytecode: the byte array that is the machine code to be executed.
        :param gas: gas budget for this transaction.
        :param failed: True if the transaction must fail
        """
        assert self._pending_transaction is None, "Already started tx"
        assert caller is not None
        self._pending_transaction = PendingTransaction(
            sort, address, price, data, caller, value, gas, None
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
        sort, address, price, data, caller, value, gas, failed = self._pending_transaction
        if issymbolic(address):

            def set_address(state, solution):
                world = state.platform
                world._pending_transaction = (
                    sort,
                    solution,
                    price,
                    data,
                    caller,
                    value,
                    gas,
                    failed,
                )

            # Assuming this condition has at least one solution
            cond = self._constraint_to_accounts(address, ty="contract", include_zero=False)
            self.constraints.add(cond)

            raise Concretize(
                "Concretizing address on transaction",
                expression=address,
                setstate=set_address,
                policy="ALL",
            )

    def _pending_transaction_concretize_caller(self):
        sort, address, price, data, caller, value, gas, failed = self._pending_transaction
        if issymbolic(caller):

            def set_caller(state, solution):
                world = state.platform
                world._pending_transaction = (
                    sort,
                    address,
                    price,
                    data,
                    solution,
                    value,
                    gas,
                    failed,
                )

            # Constrain it so it can range over all normal accounts
            # TODO: document and log this is loosing completness
            cond = self._constraint_to_accounts(caller, ty="normal")

            self.constraints.add(cond)
            raise Concretize(
                "Concretizing caller on transaction",
                expression=caller,
                setstate=set_caller,
                policy="ALL",
            )

    def _pending_transaction_failed(self):
        sort, address, price, data, caller, value, gas, failed = self._pending_transaction

        # Initially the failed flag is not set. For now we need the caller to be
        # concrete so the caller balance is easy to get. Initialize falied here
        if failed is None:
            # Check depth
            failed = self.depth >= 1024
            # Fork on enough funds for value and gas
            if not failed:
                aux_src_balance = Operators.ZEXTEND(self.get_balance(caller), 512)
                aux_value = Operators.ZEXTEND(value, 512)
                enough_balance = Operators.UGE(aux_src_balance, aux_value)
                if self.depth == 0:
                    # take the gas from the balance
                    aux_price = Operators.ZEXTEND(price, 512)
                    aux_gas = Operators.ZEXTEND(gas, 512)
                    aux_fee = aux_price * aux_gas
                    # Iff a human tx debit the fee
                    enough_balance = Operators.AND(
                        enough_balance, Operators.UGE(aux_src_balance - aux_value, aux_fee)
                    )
                failed = Operators.NOT(enough_balance)
            self._pending_transaction = sort, address, price, data, caller, value, gas, failed

        if issymbolic(failed):
            # optimistic/pesimistic is inverted as the expresion represents fail
            policy = {"optimistic": "PESSIMISTIC", "pessimistic": "OPTIMISTIC"}.get(
                consts.txfail, "ALL"
            )

            def set_failed(state, solution):
                world = state.platform
                world._pending_transaction = (
                    sort,
                    address,
                    price,
                    data,
                    caller,
                    value,
                    gas,
                    solution,
                )

            raise Concretize(
                "Concretizing tx-fail on transaction",
                expression=failed,
                setstate=set_failed,
                policy=policy,
            )

        if self.depth != 0:
            price = 0
        aux_price = Operators.ZEXTEND(price, 512)
        aux_gas = Operators.ZEXTEND(gas, 512)
        tx_fee = Operators.ITEBV(512, self.depth == 0, aux_price * aux_gas, 0)
        aux_src_balance = Operators.ZEXTEND(self.get_balance(caller), 512)
        aux_value = Operators.ZEXTEND(value, 512)
        enough_balance = Operators.UGE(aux_src_balance, aux_value + tx_fee)
        return failed

    def _process_pending_transaction(self):
        # Nothing to do here if no pending transactions
        if self._pending_transaction is None:
            return
        sort, address, price, data, caller, value, gas, failed = self._pending_transaction
        # caller
        self._pending_transaction_concretize_caller()
        # to/address
        self._pending_transaction_concretize_address()
        # check onough balance for the value
        failed = self._pending_transaction_failed()

        # done concretizing stuff
        self._pending_transaction = None

        if not failed:
            self._open_transaction(sort, address, price, data, caller, value, gas=gas)
        else:
            tx = Transaction(
                sort, address, price, data, caller, value, depth=self.depth + 1, gas=gas
            )
            tx.set_result("TXERROR")
            self._transactions.append(tx)

    def dump(self, stream, state, mevm, message):
        from ..ethereum.manticore import calculate_coverage, flagged

        blockchain = state.platform
        last_tx = blockchain.last_transaction

        stream.write("Message: %s\n" % message)
        stream.write("Last exception: %s\n" % state.context.get("last_exception", "None"))

        if last_tx:
            at_runtime = last_tx.sort != "CREATE"
            address, offset, at_init = state.context.get("evm.trace", ((None, None, None),))[-1]
            assert last_tx.result is not None or at_runtime != at_init

            # Last instruction if last tx was valid
            if str(state.context["last_exception"]) != "TXERROR":
                metadata = mevm.get_metadata(blockchain.last_transaction.address)
                if metadata is not None and address is not None:
                    stream.write("Last instruction at contract %x offset %x\n" % (address, offset))
                    source_code_snippet = metadata.get_source_for(offset, at_runtime)
                    if source_code_snippet:
                        stream.write("    ".join(source_code_snippet.splitlines(True)))
                    stream.write("\n")

        # Accounts summary
        assert state.can_be_true(True)
        is_something_symbolic = False
        stream.write("%d accounts.\n" % len(blockchain.accounts))
        for account_address in blockchain.accounts:
            is_account_address_symbolic = issymbolic(account_address)
            account_address = state.solve_one(account_address, constrain=True)

            stream.write("* %s::\n" % mevm.account_name(account_address))
            stream.write(
                "Address: 0x%x %s\n" % (account_address, flagged(is_account_address_symbolic))
            )
            balance = blockchain.get_balance(account_address)

            if not consts.ignore_balance:
                is_balance_symbolic = issymbolic(balance)
                is_something_symbolic = is_something_symbolic or is_balance_symbolic
                balance = state.solve_one(balance, constrain=True)
                stream.write("Balance: %d %s\n" % (balance, flagged(is_balance_symbolic)))

            storage = blockchain.get_storage(account_address)
            concrete_indexes = []
            if len(storage.written) > 0:
                concrete_indexes = state.solve_one_n_batched(storage.written, constrain=True)

            concrete_values = []
            if len(concrete_indexes) > 0:
                concrete_values = state.solve_one_n_batched(concrete_indexes, constrain=True)

            assert len(concrete_indexes) == len(concrete_values)
            for index, value in zip(concrete_indexes, concrete_values):
                stream.write(f"storage[{index:x}] = {value:x}\n")

            storage = blockchain.get_storage(account_address)
            stream.write("Storage: %s\n" % translate_to_smtlib(storage, use_bindings=False))

            if consts.sha3 is consts.sha3.concretize:
                all_used_indexes = []
                with state.constraints as temp_cs:
                    # make a free symbolic idex that could address any storage slot
                    index = temp_cs.new_bitvec(256)
                    # get the storage for account_address
                    storage = blockchain.get_storage(account_address)
                    # we are interested only in used slots
                    # temp_cs.add(storage.get(index) != 0)
                    temp_cs.add(storage.is_known(index))
                    # Query the solver to get all storage indexes with used slots
                    self._publish("will_solve", temp_cs, index, "get_all_values")
                    all_used_indexes = SelectedSolver.instance().get_all_values(temp_cs, index)
                    self._publish("did_solve", temp_cs, index, "get_all_values", all_used_indexes)

                if all_used_indexes:
                    stream.write("Storage:\n")
                    for i in all_used_indexes:
                        value = storage.get(i)
                        is_storage_symbolic = issymbolic(value)
                        stream.write(
                            "storage[%x] = %x %s\n"
                            % (
                                state.solve_one(i, constrain=True),
                                state.solve_one(value, constrain=True),
                                flagged(is_storage_symbolic),
                            )
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
