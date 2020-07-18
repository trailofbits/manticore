from ..core.state import StateBase


class State(StateBase):
    def execute(self):
        super().execute()
        return self._platform.execute()
