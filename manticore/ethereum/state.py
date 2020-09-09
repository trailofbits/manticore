from ..core.state import StateBase
from ..core.plugin import StateDescriptor


class State(StateBase):
    def execute(self):
        super().execute()
        return self._platform.execute()

    def _update_state_descriptor(self, descriptor: StateDescriptor, *args, **kwargs):
        """
        Called on execution_intermittent to update the descriptor for this state.
        This one should apply any EVM-specific information to the descriptor.

        :param descriptor: StateDescriptor for this state
        """
        super()._update_state_descriptor(descriptor, *args, **kwargs)
        descriptor.pc = (self.platform.current_vm.address, self.platform.current_vm.pc)
