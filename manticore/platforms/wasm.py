from .platform import Platform
from ..wasm.module_structure import Module
from ..wasm.runtime_structure import ModuleInstance, Store, FuncAddr, HostFunc, Stack
from ..core.state import TerminateState
from ..core.smtlib import ConstraintSet

def stub(*args):
    print("Called stub function with args:", args)
    if not len(args):
        return [13]
    return [0]

class WASMWorld(Platform):  # TODO: Should this just inherit Eventful instead?
    def __init__(self, filename, **kwargs):
        super().__init__(filename, **kwargs)

        self.module: Module = Module.load(filename)
        self.store = Store()
        self.instance = ModuleInstance()
        self.stack = Stack()
        self.constraints = ConstraintSet()
        imports = []
        for i in self.module.imports:
            # TODO - create function stubs that have the correct signatures
            self.store.funcs.append(HostFunc(self.module.types[i.desc], stub))
            imports.append(FuncAddr(len(self.store.funcs) - 1))
        self.instance.instantiate(self.store, self.module, imports)
        self.instance.invoke_by_name("main", self.stack, self.store, [])

    def __getstate__(self):
        state = super().__getstate__()
        state["module"] = self.module
        state["store"] = self.store
        state["instance"] = self.instance
        state["stack"] = self.stack
        state["constraints"] = self.constraints
        return state

    def __setstate__(self, state):
        self.module = state["module"]
        self.store = state["store"]
        self.instance = state["instance"]
        self.stack = state["stack"]
        self.constraints = state["constraints"]
        super().__setstate__(state)

    def start(self):
        """
        Calls the start function. Requires manual invocation
        :return:
        """
        pass

    def execute(self):
        """
        """
        # Handle interrupts et al in a try/except here
        # self.current.execute()
        if not self.instance.exec_instruction(self.store, self.stack):
            raise TerminateState("Done!")
