from manticore.core.plugin import Plugin


class UnicornEmulatePlugin(Plugin):
    """Manticore plugin to speed up emulation using unicorn until `start`"""

    def __init__(self, start: int):
        super().__init__()
        self.start = start

    def will_run_callback(self, ready_states):
        for state in ready_states:
            state.cpu.emulate_until(self.start)
