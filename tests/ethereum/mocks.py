from manticore.platforms.evm import EVMWorld

from manticore.ethereum import State

from manticore.core.smtlib import ConstraintSet


def make_mock_evm_state():
    cs = ConstraintSet()
    fakestate = State(cs, EVMWorld(cs))
    return fakestate
