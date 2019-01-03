import logging
from contextlib import contextmanager

logger = logging.getLogger(__name__)


class Plugin:
    """
    NOTE: Example plugins can be found in corresponding target's plugins.py file (native, ethereum)
    """
    def __init__(self):
        self.manticore = None

    @contextmanager
    def locked_context(self, key=None, value_type=list):
        """
        A context manager that provides safe parallel access to the global Manticore context.
        This should be used to access the global Manticore context
        when parallel analysis is activated. Code within the `with` block is executed
        atomically, so access of shared variables should occur within.
        """
        plugin_context_name = str(type(self))
        with self.manticore.locked_context(plugin_context_name, dict) as context:
            assert value_type in (list, dict, set)
            ctx = context.get(key, value_type())
            yield ctx
            context[key] = ctx

    @property
    def context(self):
        """Convenient access to shared context"""
        plugin_context_name = str(type(self))
        if plugin_context_name not in self.manticore.context:
            self.manticore.context[plugin_context_name] = {}
        return self.manticore.context[plugin_context_name]

    def on_register(self):
        """Called by parent manticore on registration"""
        pass

    def on_unregister(self):
        """Called be parent manticore on un-registration"""
        pass
