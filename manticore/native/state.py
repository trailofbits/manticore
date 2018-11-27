from manticore.core.cpu.abstractcpu import ConcretizeRegister
from manticore.core.state import StateBase, Concretize, TerminateState
from manticore.native.memory import ConcretizeMemory, MemoryException


class State(StateBase):

    def execute(self):
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
            raise Concretize(str(e),
                             expression=expression,
                             setstate=setstate,
                             policy=e.policy)
        except ConcretizeMemory as e:
            expression = self.cpu.read_int(e.address, e.size)

            def setstate(state, value):
                state.cpu.write_int(setstate.e.address, value, setstate.e.size)

            setstate.e = e
            raise Concretize(str(e),
                             expression=expression,
                             setstate=setstate,
                             policy=e.policy)
        except MemoryException as e:
            raise TerminateState(str(e), testcase=True)

        # Remove when code gets stable?
        assert self.platform.constraints is self.constraints

        return result
