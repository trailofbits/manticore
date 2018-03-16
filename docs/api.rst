API Reference
=============


This API is under active development, and should be considered unstable.

Helpers
-------

.. automodule:: manticore
   :members: issymbolic, variadic

Manticore
---------

.. autoclass:: manticore.Manticore
   :members: add_hook, hook, run, terminate, verbosity, locked_context, linux, decree, evm, init

State
-----

.. autoclass:: manticore.core.state.State
   :members: abandon, constrain, new_symbolic_buffer, new_symbolic_value, solve_n, solve_one, solve_buffer, symbolicate_buffer, invoke_model, generate_testcase

SLinux
------

Symbolic Linux

.. autoclass:: manticore.platforms.linux.SLinux
   :members: add_symbolic_file

Cpu
---

.. autoclass:: manticore.core.cpu.abstractcpu.Cpu
   :members: read_int, read_bytes, write_int, write_bytes, write_register, read_register, all_registers

Models
------

.. automodule:: manticore.models

   .. function:: strlen

   .. function:: strcmp

EVM
---
.. automodule:: manticore.platforms.evm
.. autoclass:: manticore.ethereum.ABI
   :members:
.. autoclass:: manticore.ethereum.ManticoreEVM
   :members:

EVM Assembler
-------------
.. autoclass:: manticore.platforms.evm::EVMAsm.Instruction
    :members: 
.. autoclass:: manticore.platforms.evm.EVMAsm
    :members: 

