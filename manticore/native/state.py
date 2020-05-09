from collections import namedtuple

from ..core.state import StateBase, Concretize, TerminateState
from ..native.memory import ConcretizeMemory, MemoryException


CheckpointData = namedtuple("CheckpointData", "pc, last_pc")


class State(StateBase):
    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)
        self._checkpoint_data = self._checkpoint()

    def __getstate__(self):
        state = super().__getstate__()
        state["_checkpoint_data"] = self._checkpoint_data
        return state

    def __setstate__(self, state):
        super().__setstate__(state)
        self._checkpoint_data = state["_checkpoint_data"]

    @property
    def cpu(self):
        """
        Current cpu state
        """
        return self._platform.current

    @property
    def mem(self):
        """
        Current virtual memory mappings
        """
        return self._platform.current.memory

    def _checkpoint(self) -> CheckpointData:
        """
        Checkpoint all necessary information in the case of a rollback.
        """
        self._checkpoint_data = CheckpointData(pc=self.cpu.PC, last_pc=self.cpu._last_pc)
        return self._checkpoint_data

    def execute(self):
        """
        Perform a single step on the current state
        """
        from .cpu.abstractcpu import (
            ConcretizeRegister,
        )  # must be here, otherwise we get circular imports

        self._checkpoint()
        try:
            result = self._platform.execute()

        # Instead of State importing SymbolicRegisterException and SymbolicMemoryException
        # from cpu/memory shouldn't we import Concretize from linux, cpu, memory ??
        # We are forcing State to have abstractcpu
        except ConcretizeRegister as e:
            # Need to define local variables to use in closure
            e_reg_name = e.reg_name
            e_rollback = e.rollback
            expression = self.cpu.read_register(e_reg_name)

            def setstate(state, value):
                state.cpu.write_register(e_reg_name, value)
                if e_rollback:
                    state.cpu.PC = self._checkpoint_data.pc
                    state.cpu._last_pc = self._checkpoint_data.last_pc

            raise Concretize(str(e), expression=expression, setstate=setstate, policy=e.policy)
        except ConcretizeMemory as e:
            # Need to define local variables to use in closure
            e_address = e.address
            e_size = e.size
            e_rollback = e.rollback
            expression = self.cpu.read_int(e_address, e_size)

            def setstate(state, value):
                state.cpu.write_int(e_address, value, e_size)
                if e_rollback:
                    state.cpu.PC = self._checkpoint_data.pc
                    state.cpu._last_pc = self._checkpoint_data.last_pc

            raise Concretize(str(e), expression=expression, setstate=setstate, policy=e.policy)
        except MemoryException as e:
            raise TerminateState(str(e), testcase=True)

        # Remove when code gets stable?
        assert self.platform.constraints is self.constraints

        return result

    def invoke_model(self, model):
        """
        Invokes a `model`. Modelling can be used to override a function in the target program with a custom
        implementation.

        For more information on modelling see docs/models.rst

        A `model` is a callable whose first argument is a `manticore.native.State` instance.
        If the following arguments correspond to the arguments of the C function
        being modeled. If the `model` models a variadic function, the following argument
        is a generator object, which can be used to access function arguments dynamically.
        The `model` callable should simply return the value that should be returned by the
        native function being modeled.f

        :param model: callable, model to invoke
        """
        self._platform.invoke_model(model, prefix_args=(self,))
