Internal classes
================

The following classes are considered Manticore-internal. Their interface should be relied on.

Store
-----

 .. autoclass:: manticore.core.workspace.Store
    :members: fromdescriptor, save_value, load_value, save_stream, load_stream, save_state, load_state, rm, ls

Workspace
---------

 .. autoclass:: manticore.core.workspace.Workspace
    :members: try_loading_workspace, load_state, save_state

  
