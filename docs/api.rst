API
===


This API is under active development, and should be considered unstable.

Helpers
-------

.. autofunction:: manticore.issymbolic

Manticore
---------

.. autoclass:: manticore.Manticore
   :members:

State
-----

.. autoclass:: manticore.core.state.State
   :members:

Cpu
---

.. autoclass:: manticore.core.cpu.abstractcpu.Cpu
   :members: read_int, read_bytes, write_int, write_bytes, write_register, read_register, all_registers

