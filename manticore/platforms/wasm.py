from .platform import Platform
from ..wasm.module_structure import Module
from ..wasm.runtime_structure import ModuleInstance, Store, FuncAddr, HostFunc, Stack
from ..core.state import TerminateState


def stub(*args, **kwargs):
    print("Called stub function")
    return 0


class WASMWorld(Platform):  # TODO: Should this just inherit Eventful instead?
    def __init__(self, filename, **kwargs):
        super().__init__(filename, **kwargs)

        self.module: Module = Module.load(filename)
        self.store = Store()
        self.instance = ModuleInstance()
        self.stack = Stack()
        imports = []
        for i in self.module.imports:
            # TODO - create function stubs that have the correct signatures
            self.store.funcs.append(HostFunc(self.module.types[i.desc], stub))
            imports.append(FuncAddr(len(self.store.funcs) - 1))
        self.instance.instantiate(self.store, self.module, imports)
        print(self.instance.invoke_by_name("main", self.stack, self.store, []))

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
        # self.instance.invoke_by_name("main", self.stack, self.store, [])
        raise TerminateState("Done!")
