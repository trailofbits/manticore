Native
------

Platforms
^^^^^^^^^
.. autoclass:: manticore.native.Manticore
   :members: linux, decree
   :noindex:

Linux
^^^^^
.. autoclass:: manticore.platforms.linux.SLinux
   :members: add_symbolic_file
   :undoc-members:


Models
^^^^^^

.. automodule:: manticore.native.models
   :members:
   :undoc-members:

State
^^^^^

.. autoclass:: manticore.native.state.State
   :members:
   :undoc-members:

Cpu
^^^

.. autoclass:: manticore.native.state.State
   :members: cpu
   :undoc-members:
   :noindex:

.. autoclass:: manticore.native.cpu.abstractcpu.Cpu
   :members:
   :undoc-members:

Memory
^^^^^^

.. autoclass:: manticore.native.state.State
   :members: mem
   :undoc-members:
   :noindex:

.. autoclass:: manticore.native.memory.SMemory
   :members:

State
^^^^^

.. autoclass:: manticore.native.state.State
   :members:
   :undoc-members:
   :noindex:

Function Models
^^^^^^^^^^^^^^^

The Manticore function modeling API can be used to override a certain
function in the target program with a custom implementation in Python.
This can greatly increase performance.

Manticore comes with implementations of function models for some common library routines (core models),
and also offers a user API for defining user-defined models.

To use a core model, use the :meth:`~manticore.native.state.State.invoke_model` API. The
available core models are documented in the API Reference::

    from manticore.native.models import strcmp
    addr_of_strcmp = 0x400510
    @m.hook(addr_of_strcmp)
    def strcmp_model(state):
        state.invoke_model(strcmp)

To implement a user-defined model, implement your model as a Python function, and pass it to
:meth:`~manticore.native.state.State.invoke_model`. See the
:meth:`~manticore.native.state.State.invoke_model` documentation for more. The
`core models <https://github.com/trailofbits/manticore/blob/master/manticore/models.py>`_
are also good examples to look at and use the same external user API.

Symbolic Input
^^^^^^^^^^^^^^

Manticore allows you to execute programs with symbolic input, which represents a range of possible inputs. You
can do this in a variety of manners.

**Wildcard byte**

Throughout these various interfaces, the '+' character is defined to designate a byte
of input as symbolic. This allows the user to make input that mixes symbolic and concrete
bytes (e.g. known file magic bytes).

For example: ``"concretedata++++++++moreconcretedata++++++++++"``

**Symbolic arguments/environment**

To provide a symbolic argument or environment variable on the command line,
use the wildcard byte where arguments and environment are specified.::

    $ manticore ./binary +++++ +++++
    $ manticore ./binary --env VAR1=+++++ --env VAR2=++++++

For API use, use the ``argv`` and ``envp`` arguments to the :meth:`manticore.native.Manticore.linux` classmethod.::

    Manticore.linux('./binary', ['++++++', '++++++'], dict(VAR1='+++++', VAR2='++++++'))

**Symbolic stdin**

Manticore by default is configured with 256 bytes of symbolic stdin data which is configurable
with the ``stdin_size`` kwarg of :meth:`manticore.native.Manticore.linux` , after an optional
concrete data prefix, which can be provided with the ``concrete_start`` kwarg of
:meth:`manticore.native.Manticore.linux`.

**Symbolic file input**

To provide symbolic input from a file, first create the files that will be opened by the
analyzed program, and fill them with wildcard bytes where you would like symbolic data
to be.

For command line use, invoke Manticore with the ``--file`` argument.::

    $ manticore ./binary --file my_symbolic_file1.txt --file my_symbolic_file2.txt

For API use, use the :meth:`~manticore.platforms.linux.SLinux.add_symbolic_file` interface to customize the initial
execution state from an :meth:`~manticore.core.manticore.ManticoreBase.__init__`

.. code-block:: Python

    @m.init
    def init(initial_state):
        initial_state.platform.add_symbolic_file('my_symbolic_file1.txt')

**Symbolic sockets**

Manticore's socket support is experimental! Sockets are configured to contain 64 bytes of
symbolic input.
