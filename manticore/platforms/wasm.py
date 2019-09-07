from .platform import Platform
from ..wasm.module_structure import Module
from ..wasm.runtime_structure import ModuleInstance, Store, FuncAddr, HostFunc, Stack
from ..wasm.types import Trap
from ..core.state import TerminateState
from ..core.smtlib import ConstraintSet, issymbolic
from ..core.smtlib.solver import Z3Solver
from functools import partial
import typing, types
import logging

logger = logging.getLogger(__name__)


def stub(arity, *args):
    logger.info("Called stub function with args:", args)
    return [0 for _ in range(arity)]


class WASMWorld(Platform):  # TODO: Should this just inherit Eventful instead?
    def __init__(self, filename, **kwargs):
        super().__init__(filename, **kwargs)

        self.module: Module = Module.load(filename)
        self.store = Store()
        self.instance = ModuleInstance()
        self.stack = Stack()
        self.constraints = ConstraintSet()
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

    def instantiate(self, import_dict: typing.Dict[str, types.FunctionType]):
        imports = []
        for i in self.module.imports:
            # TODO - create function stubs that have the correct signatures
            func_type = self.module.types[i.desc]
            self.store.funcs.append(
                HostFunc(
                    func_type, import_dict.get(i.name, partial(stub, len(func_type.result_types)))
                )
            )
            imports.append(FuncAddr(len(self.store.funcs) - 1))
        self.instance.instantiate(self.store, self.module, imports)
        self.instantiated = True

    def invoke(self, name="main", argv=[]):
        self.instance.invoke_by_name(name, self.stack, self.store, list(argv))

    def exec_for_test(self, funcname):
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
        """
        # Handle interrupts et al in a try/except here
        # self.current.execute()
        if not self.instantiated:
            raise RuntimeError("Trying to execute before instantiation!")
        if not self.instance.exec_instruction(self.store, self.stack):
            ret = None
            if not self.stack.empty():
                ret = self.stack.pop()
                print("WASM Execution returned", ret)
                if issymbolic(ret):
                    print(
                        "Symbolic return detected, possible values:",
                        Z3Solver.instance().get_all_values(self.constraints, ret),
                    )

            raise TerminateState(f"Execution returned {ret}")
