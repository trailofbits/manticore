Function Models
===============

The Manticore function modeling API can be used to override a certain
function in the target program with a custom implementation in Python.
This can greatly increase performance.

Manticore comes with implementations of function models for some common library routines (core models),
and also offers a user API for defining user-defined models.

To use a core model, use the :meth:`~manticore.core.state.State.invoke_model` API. The
available core models are documented in the API Reference::

    from manticore.models import strcmp
    addr_of_strcmp = 0x400510
    @m.hook(addr_of_strcmp)
    def strcmp_model(state):
        state.invoke_model(strcmp)

To implement a user-defined model, implement your model as a Python function, and pass it to
:meth:`~manticore.core.state.State.invoke_model`. See the
:meth:`~manticore.core.state.State.invoke_model` documentation for more. The
`core models <https://github.com/trailofbits/manticore/blob/master/manticore/models.py>`_
are also good examples to look at and use the same external user API.





