from manticore.core.state import BaseState


class State(BaseState):
    def execute(self):
        return self._platform.execute()
