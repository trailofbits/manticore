from ..core.state import StateBase


class State(StateBase):
    def execute(self):
        return self._platform.execute()
