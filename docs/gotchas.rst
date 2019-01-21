Gotchas
=======

Manticore has a number of "gotchas": quirks or little things you need to do in a certain way otherwise you'll have crashes and other unexpected results.

Mutable context entries
-----------------------

Something like ``m.context['flag'].append('a')`` inside a hook will not work. You need to (unfortunately, for now) do ``m.context['flag'] += ['a']``. This is related to
Manticore's built in support for parallel analysis and use of the `multiprocessing` library. This gotcha is specifically related to this note from the Python
`documentation <https://docs.python.org/2.7/library/multiprocessing.html#multiprocessing.managers.SyncManager.list>`_ :

    "Note: Modifications to mutable values or items in dict and list proxies will not be propagated through the manager, because the proxy has no way of knowing when its values or items are modified. To modify such an item, you can re-assign the modified object to the container proxy"


Context locking
---------------

Manticore natively supports parallel analysis; if this is activated, client code should always be careful to properly lock the global context when accessing it.

An example of a global context race condition, when modifying two context entries.::

    m.context['flag1'] += ['a']
    --- interrupted by other worker
    m.context['flag2'] += ['b']

Client code should use the :meth:`~manticore.core.ManticoreBase.locked_context` API::

    with m.locked_context() as global_context:
        global_context['flag1'] += ['a']
        global_context['flag2'] += ['b']


"Random" Policy
---------------

The `random` policy, which is the Manticore default, is not actually random and is instead deterministically seeded. This means that running the same analysis twice should return the same results (and get stuck in the same places).
