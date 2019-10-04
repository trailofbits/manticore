from .platform import Platform
from ..wasm.module_structure import Module
from ..wasm.runtime_structure import (
    ModuleInstance,
    Store,
    FuncAddr,
    HostFunc,
    Stack,
    MemInst,
    MemAddr,
    GlobalInst,
    GlobalAddr,
    TableInst,
    TableAddr,
    ExternVal,
)
from ..wasm.types import Trap, TypeIdx, TableType, MemoryType, GlobalType
from ..core.state import TerminateState
from ..core.smtlib import ConstraintSet, issymbolic
from ..core.smtlib.solver import Z3Solver
from functools import partial
import typing
import types
import logging

logger = logging.getLogger(__name__)


def stub(arity, _constraints, *args):
    """Default function used for hostfunc calls when a proper import wasn't provided """
    logger.info("Called stub function with args: %s", args)
    return [0 for _ in range(arity)]


class WASMWorld(Platform):
    """Manages global environment for a WASM state. Analagous to EVMWorld."""

    def __init__(self, filename, **kwargs):
        """
        :param filename: The WASM module to execute
        :param kwargs: Accepts "constraints" to pass in an initial ConstraintSet
        """
        super().__init__(filename, **kwargs)
        #: Initial set of constraints
        self.constraints = kwargs.get("constraints", ConstraintSet())
        #: Read-only reference to the WASM module, parsed by the wasm (Python) module
        self.module: Module = Module.load(filename)
        #: Backing store for functions, memories, tables, and globals
        self.store = Store()
        #: Does the bulk of the work of executing instructions
        self.instance = ModuleInstance(self.constraints)
        #: Stores numeric values, branch labels, and execution frames
        self.stack = Stack()
        #: Prevents users from calling run without instantiating the module
        self.instantiated = False

    def __getstate__(self):
        state = super().__getstate__()
        state["module"] = self.module
        state["store"] = self.store
        state["instance"] = self.instance
        state["stack"] = self.stack
        state["constraints"] = self.constraints
        state["instantiated"] = self.instantiated
        return state

    def __setstate__(self, state):
        self.module = state["module"]
        self.store = state["store"]
        self.instance = state["instance"]
        self.stack = state["stack"]
        self.constraints = state["constraints"]
        self.instantiated = state["instantiated"]
        super().__setstate__(state)

    def instantiate(self, import_dict: typing.Dict[str, types.FunctionType], exec_start=False):
        """
        Prepares the underlying ModuleInstance for execution. Generates stub imports for globals and memories.
        Throws NotImplementedError if the module attempts to import a table.

        :param import_dict: Dict mapping strings to functions. Functions should accept the current ConstraintSet as
        the first argument.
        :param exec_start: Whether or not to automatically execute the `start` function, if it is set.
        :return: None
        """
        imports: typing.List[ExternVal] = []
        for i in self.module.imports:
            if isinstance(i.desc, TypeIdx):
                func_type = self.module.types[i.desc]
                self.store.funcs.append(
                    HostFunc(
                        func_type,
                        import_dict.get(i.name, partial(stub, len(func_type.result_types))),
                    )
                )
                imports.append(FuncAddr(len(self.store.funcs) - 1))
            elif isinstance(i.desc, TableType):
                raise NotImplementedError("Currently unable to handle imported TableTypes")
            elif isinstance(i.desc, MemoryType):
                self.store.mems.append(
                    MemInst(
                        [
                            0x0 for _i in range(max(i.desc.min, 1) * (64 * 1024))
                        ],  # TODO - these should be symbolic, and the user should be able to provide them.
                        i.desc.max,
                    )
                )
                imports.append(MemAddr(len(self.store.mems) - 1))
            elif isinstance(i.desc, GlobalType):
                self.store.globals.append(
                    GlobalInst(i.desc.value(0), i.desc.mut)
                )  # TODO - let the user specify the value
                imports.append(GlobalAddr(len(self.store.globals) - 1))

        self.instance.instantiate(self.stack, self.store, self.module, imports, exec_start)
        self.instantiated = True

    def invoke(self, name="main", argv=[]):
        """
        Sets up the WASMWorld to run the function specified by `name` when `ManticoreWASM.run` is called

        :param name: Name of the function to invoke
        :param argv: List of arguments to pass to the function. Should typically be I32, I64, F32, or F64
        :return: None
        """
        self.instance.invoke_by_name(name, self.stack, self.store, list(argv))

    def exec_for_test(self, funcname):
        """
        Helper method that simulates the evaluation loop without creating workers or states, forking, or concretizing
        symbolic values.
        Only used for concrete unit testing.

        :param funcname: The name of the function to test
        :return: The top n items from the stack where n is the expected number of return values from the function
        """
        rets = 0
        for export in self.instance.exports:
            if export.name == funcname and isinstance(export.value, FuncAddr):
                rets = len(self.store.funcs[export.value].type.result_types)

        try:
            while self.instance.exec_instruction(self.store, self.stack):
                pass
            if rets == 0:
                return []
            if rets == 1:
                return [self.stack.pop()]
            else:
                return [self.stack.pop() for _i in range(rets)]
        except (Trap, NotImplementedError) as e:
            self.instance.reset_internal()
            self.stack = Stack()
            raise e

    def execute(self):
        """
        Tells the underlying ModuleInstance to execute a single WASM instruction. Raises TerminateState if there are
        no more instructions to execute, or if the instruction raises a Trap.
        """
        if not self.instantiated:
            raise RuntimeError("Trying to execute before instantiation!")
        try:
            if not self.instance.exec_instruction(self.store, self.stack):
                raise TerminateState(f"Execution returned {self.stack.peek()}")
        except Trap as e:
            raise TerminateState(f"Execution raised Trap: {str(e)}")
