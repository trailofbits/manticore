from typing import Optional

from .abi import ABI
from ..exceptions import EthereumError


class EVMAccount(object):
    def __init__(self, address=None, manticore=None, name=None):
        """ Encapsulates an account.

            :param address: the address of this account
            :type address: 160 bit long integer
            :param manticore: the controlling Manticore

        """
        self._manticore = manticore
        self._address = address
        self._name = name

    def __eq__(self, other):
        if isinstance(other, int):
            return self._address == other
        if isinstance(self, EVMAccount):
            return self._address == other._address
        return super().__eq__(other)

    @property
    def name(self):
        return self._name

    @property
    def address(self):
        return self._address

    def __int__(self):
        return self._address

    def __str__(self):
        return str(self._address)


class EVMContract(EVMAccount):
    """ An EVM account

        Note: The private methods of this class begin with a double underscore to
        avoid function name collisions with Solidity functions that begin with
        a single underscore
    """

    def __init__(self, default_caller=None, **kwargs):
        """ Encapsulates a contract account.
            :param default_caller: the default caller address for any transaction

        """
        super().__init__(**kwargs)
        self._default_caller = default_caller
        self._hashes = None

    def add_function(self, signature):
        func_id = ABI.function_selector(signature)
        func_name = str(signature.split('(')[0])
        if func_name.startswith('__') or func_name in {'add_function', 'address', 'name'}:
            # TODO(mark): is this actually true? is there anything actually wrong with a solidity name beginning w/ an underscore?
            raise EthereumError("Function name ({}) is internally reserved".format(func_name))
        if func_name in self._hashes:
            self._hashes[func_name].append((signature, func_id))
            return
        if func_id in {h[1] for names in self._hashes.values() for h in names}:
            raise EthereumError("A function with the same hash as {} is already defined".format(func_name))
        self._hashes[func_name] = [(signature, func_id)]

    def __null_func(self):
        pass

    def __init_hashes(self):
        #initializes self._hashes lazy
        if self._hashes is None and self._manticore is not None:
            self._hashes = {}
            md = self._manticore.get_metadata(self._address)
            if md is not None:
                for signature in md.functions:
                    self.add_function(signature)
            # It was successful, no need to re-run. _init_hashes disabled
            self.__init_hashes = self.__null_func

    def __getattribute__(self, name):
        """ If this is a contract account of which we know the functions hashes,
            this will build the transaction for the function call.

            Example use::

                #call function `add` on contract_account with argument `1000`
                contract_account.add(1000)

        """
        if not name.startswith('_'):
            self.__init_hashes()
            if self._hashes is not None and name in self._hashes.keys():
                def f(*args, signature: Optional[str]=None, caller=None, value=0, **kwargs):
                    try:
                        if signature:
                            if f'{name}{signature}' not in {h[0] for names in self._hashes.values() for h in names}:
                                raise EthereumError(
                                    f'Function: `{name}` has no such signature`\n'
                                    f'Known signatures: {[x[0][len(name):] for x in self._hashes[name]]}')

                            tx_data = ABI.function_call(f'{name}{signature}', *args)
                        else:
                            if len(self._hashes[name]) > 1:
                                sig = self._hashes[name][0][0][len(name):]
                                raise EthereumError(
                                    f'Function: `{name}` has multiple signatures but `signature` is not '
                                    f'defined! Example: `account.{name}(..., signature="{sig}")`\n'
                                    f'Known signatures: {[x[0][len(name):] for x in self._hashes[name]]}')

                            tx_data = ABI.function_call(str(self._hashes[name][0][0]), *args)
                    except KeyError as e:
                        raise e

                    if caller is None:
                        caller = self._default_caller

                    self._manticore.transaction(caller=caller,
                                                address=self._address,
                                                value=value,
                                                data=tx_data)
                return f

        return object.__getattribute__(self, name)