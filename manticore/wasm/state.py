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

    @property
    def globals(self):
        """
        The set of globals in the current execution Store
        """
        return self.store.globals

    @property
    def locals(self):
        """
        The set of locals in the current execution frame.

        There may not be a frame on the stack if this is called at the wrong time.
        """
        frame = self.stack.get_frame()
        frame = getattr(frame, "frame", frame)
        return frame.locals

    def execute(self):
        return self._platform.execute(self)
