from .platform import Platform
from ..wasm.structure import Module
from ..core.state import TerminateState


class WASMWorld(Platform):  # TODO: Should this just inherit Eventful instead?
    def __init__(self, filename, **kwargs):
        super().__init__(filename, **kwargs)

        self.module: Module = Module.load(filename)

    def execute(self):
        """
        """
        # Handle interrupts et al in a try/except here
        # self.current.execute()
        raise TerminateState("Done!")
