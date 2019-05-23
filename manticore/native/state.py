from ..core.state import StateBase, Concretize, TerminateState
from ..native.memory import ConcretizeMemory, MemoryException


class State(StateBase):
    @property
    def cpu(self):
        return self._platform.current

    @property
    def mem(self):
        return self._platform.current.memory

    def execute(self):
        from .cpu.abstractcpu import (
            ConcretizeRegister,
        )  # must be here, otherwise we get circular imports

        try:
            result = self._platform.execute()

        # Instead of State importing SymbolicRegisterException and SymbolicMemoryException
        # from cpu/memory shouldn't we import Concretize from linux, cpu, memory ??
        # We are forcing State to have abstractcpu
        except ConcretizeRegister as e:
            expression = self.cpu.read_register(e.reg_name)

            def setstate(state, value):
                state.cpu.write_register(setstate.e.reg_name, value)

            setstate.e = e
            raise Concretize(str(e), expression=expression, setstate=setstate, policy=e.policy)
        except ConcretizeMemory as e:
            expression = self.cpu.read_int(e.address, e.size)

            def setstate(state, value):
                state.cpu.write_int(setstate.e.address, value, setstate.e.size)

            setstate.e = e
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
