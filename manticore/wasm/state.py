from ..core.state import StateBase


class State(StateBase):
    @property
    def stack(self):
        """
        Current execution Stack
        """
        return self._platform.stack

    @property
    def store(self):
        """
        Current execution Store
        """
        return self._platform.store

    @property
    def mem(self):
        """
        The first memory in the current execution Store
        """
        return self.store.mems[0]

    def execute(self):
        return self._platform.execute()
