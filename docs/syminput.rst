Symbolic Input
==============

Manticore allows you to execute programs with symbolic input, which represents a range of possible inputs. You
can do this in a variety of manners.

Wildcard byte
-------------

Throughout these various interfaces, the '+' character is defined to designate a byte
of input as symbolic. This allows the user to make input partially symbolic, and partially
concrete (e.g. known file magic bytes).

For example: "concretedata++++++++moreconcretedata++++++++++"

Symbolic arguments/environment
------------------------------

To provide a symbolic argument or environment variable on the Manticore command line,
use the wildcard byte where arguments and environment are specified.

    $ manticore binary +++++ +++++
    $ manticore binary --env VAR1=+++++ --env VAR2=++++++

For API use, use the ``argv`` and ``envp`` arguments to the ``Manticore.linux`` classmethod.

    Manticore.linux('binary', ['++++++', '++++++'], dict(VAR1='+++++', VAR2='++++++'))

Symbolic stdin
--------------

Manticore by default is configured with 256 of symbolic stdin data, after an optional
concrete data prefix, which can be provided with the ``concrete_data`` kwarg.

Symbolic file input
-------------------

To provide symbolic input from a file, first create the files that will be opened by the
analyzed program, and filling them with wildcard bytes where you would like symbolic data
to be.

For command line use, invoke Manticore with the ``--file`` argument.

    $ manticore binary --file my_symbolic_file1.txt --file my_symbolic_file2.txt

For API use, use the ``SLinux.add_symbolic_file`` interface to customize the initial
execution state from an ``init`` hook.

    @m.init
    def init(initial_state):
        initial_state.platform.add_symbolic_file('my_symbolic_file1.txt')


Symbolic sockets
----------------

Manticore's socket support is experimental! Sockets are configured to contain 64 bytes of
symbolic input.
