from collections import namedtuple
from typing import Optional

from .abi import ABI
from ..exceptions import EthereumError


HashesEntry = namedtuple("HashesEntry", "signature func_id")


class EVMAccount:
    def __init__(self, address=None, manticore=None, name=None):
        """
        Encapsulates an account.

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

    def __hash__(self):
        return self._address

    @property
    def name_(self):
        """
        This is named this way to avoid naming collisions with Solidity functions/data,
        since EVMContract inherits this.
        """
        return self._name

    @property
    def address(self):
        return self._address

    def __int__(self):
        return self._address

    def __str__(self):
        return str(self._address)

    def __format__(self, format_spec=""):
        return self._address.__format__(format_spec)


class EVMContract(EVMAccount):
    """
    An EVM account

    Note: The private methods of this class begin with a double underscore to avoid function
    name collisions with Solidity functions that begin with a single underscore.
    """

    def __init__(self, default_caller=None, **kwargs):
        """
        Encapsulates a contract account.

        :param default_caller: the default caller address for any transaction
        """
        super().__init__(**kwargs)
        self.__default_caller = default_caller
        self.__hashes = {}
        self.__initialized = False

    def add_function(self, signature):
        func_id = ABI.function_selector(signature)
        func_name = str(signature.split("(")[0])

        if func_name in self.__dict__ or func_name in {"add_function", "address", "name_"}:
            raise EthereumError(f"Function name ({func_name}) is internally reserved")

        entry = HashesEntry(signature, func_id)

        if func_name in self.__hashes:
            self.__hashes[func_name].append(entry)
            return

        if func_id in {entry.func_id for entries in self.__hashes.values() for entry in entries}:
            raise EthereumError(f"A function with the same hash as {func_name} is already defined")

        self.__hashes[func_name] = [entry]

    def __init_hashes(self):
        md = self._manticore.get_metadata(self._address)
        if md is not None:
            for signature in md.function_signatures:
                self.add_function(signature)
        # It was successful, no need to re-run. _init_hashes disabled
        self.__initialized = True

    def __getattr__(self, name):
        """
        If this is a contract account of which we know the functions hashes,
        this will build the transaction for the function call.

        Example use:
            # call function `add` on contract_account with argument `1000`
            contract_account.add(1000)
        """
        if not self.__initialized:
            self.__init_hashes()

        if name in self.__hashes:

            def f(
                *args, signature: Optional[str] = None, caller=None, value=0, gas=210000, **kwargs
            ):
                try:
                    if signature:
                        if f"{name}{signature}" not in {
                            entry.signature
                            for entries in self.__hashes.values()
                            for entry in entries
                        }:
                            raise EthereumError(
                                f"Function: `{name}` has no such signature\n"
                                f"Known signatures: {[entry.signature[len(name):] for entry in self.__hashes[name]]}"
                            )

                        tx_data = ABI.function_call(f"{name}{signature}", *args)
                    else:
                        entries = self.__hashes[name]
                        if len(entries) > 1:
                            sig = entries[0].signature[len(name) :]
                            raise EthereumError(
                                f"Function: `{name}` has multiple signatures but `signature` is not "
                                f'defined! Example: `account.{name}(..., signature="{sig}")`\n'
                                f"Known signatures: {[entry.signature[len(name):] for entry in self.__hashes[name]]}"
                            )

                        tx_data = ABI.function_call(str(entries[0].signature), *args)
                except KeyError as e:
                    raise e

                if caller is None:
                    caller = self.__default_caller

                self._manticore.transaction(
                    caller=caller, address=self._address, value=value, data=tx_data, gas=gas
                )

            return f

        raise AttributeError(f"The contract {self._name} doesn't have {name} function.")
