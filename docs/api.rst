API Reference
=============


This API is under active development, and should be considered unstable.

Core Helpers
------------

.. automodule:: manticore
   :members: issymbolic, istainted

Native Helpers
--------------

.. automodule:: manticore.native
   :members: variadic

ManticoreBase
-------------

.. autoclass:: manticore.core.manticore.ManticoreBase
   :members: add_hook, hook, run, terminate, verbosity, locked_context, init

native.Manticore
----------------

.. autoclass:: manticore.native.Manticore
   :members: linux, decree

BaseState
---------

.. autoclass:: manticore.core.state.StateBase
   :members: abandon, constrain, new_symbolic_buffer, new_symbolic_value, solve_n, solve_one, solve_buffer, symbolicate_buffer, generate_testcase


native.State
------------

.. autoclass:: manticore.native.state.State
   :members: invoke_model

SLinux
------

Symbolic Linux

.. autoclass:: manticore.platforms.linux.SLinux
   :members: add_symbolic_file

Cpu
---

.. autoclass:: manticore.native.cpu.abstractcpu.Cpu
   :members: read_int, read_bytes, write_int, write_bytes, write_register, read_register, all_registers

Models
------

.. automodule:: manticore.native.models

   .. function:: strlen

   .. function:: strcmp

EVM
---
.. automodule:: manticore.platforms.evm
.. autoclass:: manticore.ethereum.ABI
   :members:
.. autoclass:: manticore.ethereum.ManticoreEVM
   :members:
