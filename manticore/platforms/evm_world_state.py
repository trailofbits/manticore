import logging
import os
from abc import ABC, abstractmethod
from typing import Any, Dict, Set
from urllib.parse import ParseResult, urlparse
from web3 import Web3
from ..exceptions import EthereumError


logger = logging.getLogger(__name__)


class WorldState:
    @abstractmethod
    def accounts(self) -> Set[int]:
        pass

    @abstractmethod
    def get_nonce(self, address: int) -> Any:
        pass

    @abstractmethod
    def get_balance(self, address: int) -> Any:
        pass

    @abstractmethod
    def get_storage(self, address: int) -> Dict[int, Any]:
        pass

    @abstractmethod
    def get_storage_data(self, address: int, offset: int) -> Any:
        pass

    @abstractmethod
    def get_code(self, address: int) -> Any:
        pass

    @abstractmethod
    def get_blocknumber(self) -> Any:
        pass

    @abstractmethod
    def get_timestamp(self) -> Any:
        pass

    @abstractmethod
    def get_difficulty(self) -> Any:
        pass

    @abstractmethod
    def get_gaslimit(self) -> Any:
        pass

    @abstractmethod
    def get_coinbase(self) -> Any:
        pass


class DefaultWorldState(WorldState):
    def accounts(self) -> Set[int]:
        return set()

    def get_nonce(self, address: int) -> Any:
        return 0

    def get_balance(self, address: int) -> Any:
        return 0

    def get_storage(self, address: int) -> Dict[int, Any]:
        return {}

    def get_storage_data(self, address: int, offset: int) -> Any:
        return 0

    def get_code(self, address: int) -> Any:
        return bytes()

    def get_blocknumber(self) -> Any:
        # assume initial byzantium block
        return 4370000

    def get_timestamp(self) -> Any:
        # 1524785992; // Thu Apr 26 23:39:52 UTC 2018
        return 1524785992

    def get_difficulty(self) -> Any:
        return 0

    def get_gaslimit(self) -> Any:
        return 0

    def get_coinbase(self) -> Any:
        return 0


class Endpoint:
    def __init__(self, blocknumber: int, warned: bool):
        self.blocknumber = blocknumber
        self.warned = warned


_endpoints: Dict[str, Endpoint] = {}


def _web3_address(address: int) -> str:
    return Web3.toChecksumAddress("0x%0.40x" % address)


# sam.moelius: Notes:
#
# 1. https://github.com/ethereum/wiki/wiki/JSON-RPC lists the kinds of information that an Ethereum
#    node can provide over JSON RPC.
#
# 2. The accounts and get_storage methods do not make sense when using JSON RPC.  IMHO, we should
#    program to the least common denominator.  In that sense, we should see whether the accounts and
#    get_storage methods could be eliminated.


class RemoteWorldState(WorldState):
    def __init__(self, url: str):
        actual = urlparse(url)
        expected = ParseResult(scheme="", netloc="", path=url, params="", query="", fragment="")
        if actual != expected:
            raise EthereumError("URL must be of the form 'IP:PORT': " + url)
        self._url = url

    def _web3(self) -> Web3:
        web3 = Web3(Web3.WebsocketProvider("ws://" + self._url))
        blocknumber = web3.eth.blockNumber
        if self._url not in _endpoints:
            _endpoints[self._url] = Endpoint(blocknumber, False)
            logger.info("Connected to %s (blocknumber = %d)", self._url, blocknumber)
        if _endpoints[self._url].blocknumber != blocknumber:
            if not _endpoints[self._url].warned:
                logger.warning(
                    "%s blocknumber has changed (%d != %d)---someone is using the endpoint"
                    + " beside us",
                    self._url,
                    _endpoints[self._url].blocknumber,
                    blocknumber,
                )
                _endpoints[self._url].warned = True
            _endpoints[self._url].blocknumber = blocknumber
        return web3

    def accounts(self) -> Set[int]:
        raise NotImplementedError

    def get_nonce(self, address: int) -> Any:
        return self._web3().eth.getTransactionCount(_web3_address(address))

    def get_balance(self, address: int) -> Any:
        return self._web3().eth.getBalance(_web3_address(address))

    def get_storage(self, address) -> Dict[int, Any]:
        raise NotImplementedError

    def get_storage_data(self, address: int, offset: int) -> Any:
        return self._web3().eth.getStorageAt(_web3_address(address), offset)

    def get_code(self, address: int) -> Any:
        return self._web3().eth.getCode(_web3_address(address))

    def get_blocknumber(self) -> Any:
        return self._web3().eth.blockNumber

    def get_timestamp(self) -> Any:
        return self._web3().eth.timestamp

    def get_difficulty(self) -> Any:
        return self._web3().eth.difficulty

    def get_gaslimit(self) -> Any:
        return self._web3().eth.gasLimit

    def get_coinbase(self) -> Any:
        return self._web3().eth.coinbase


# sam.moelius: If we decide to cache results returned from a RemoteWorldState, then they should NOT be
# cached within an overlay.  The reason is that this could affect the results of subsequent operations.
# Consider a call to get_storage_data followed by a call to has_storage.  If nothing was written to
# storage within the overlay, then the call to has_storage will throw an exception.  But if the result
# of the call to get_storage_data was cached in the overlay, then no exception would be thrown.


class OverlayWorldState(WorldState):
    def __init__(self, underlay: WorldState):
        self._underlay: WorldState = underlay
        self._deleted_accounts: Set[int] = set()
        self._nonce: Dict[int, Any] = {}
        self._balance: Dict[int, Any] = {}
        self._storage: Dict[int, Dict[int, Any]] = {}
        self._code: Dict[int, Any] = {}
        self._blocknumber: Any = None
        self._timestamp: Any = None
        self._difficulty: Any = None
        self._gaslimit: Any = None
        self._coinbase: Any = None

    def accounts(self) -> Set[int]:
        accounts: Set[int] = set()
        try:
            accounts = self._underlay.accounts()
        except NotImplementedError:
            pass
        return (
            accounts
            | self._nonce.keys()
            | self._balance.keys()
            | self._storage.keys()
            | self._code.keys()
        ) - self._deleted_accounts

    def get_nonce(self, address: int) -> Any:
        if address in self._nonce:
            return self._nonce[address]
        else:
            return self._underlay.get_nonce(address)

    def get_balance(self, address: int) -> Any:
        if address in self._balance:
            return self._balance[address]
        else:
            return self._underlay.get_balance(address)

    def get_storage(self, address: int) -> Dict[int, Any]:
        storage: Dict[int, Any] = {}
        try:
            storage = self._underlay.get_storage(address)
        except NotImplementedError:
            pass
        if address in self._storage:
            storage.update(self._storage[address])
        return storage

    def get_storage_data(self, address: int, offset: int) -> Any:
        if address in self._storage and offset in self._storage[address]:
            return self._storage[address][offset]
        else:
            return self._underlay.get_storage_data(address, offset)

    def get_code(self, address: int) -> Any:
        if address in self._code:
            return self._code[address]
        else:
            return self._underlay.get_code(address)

    def get_blocknumber(self) -> Any:
        if self._blocknumber is not None:
            return self._blocknumber
        else:
            return self._underlay.get_blocknumber()

    def get_timestamp(self) -> Any:
        if self._timestamp is not None:
            return self._timestamp
        else:
            return self._underlay.get_timestamp()

    def get_difficulty(self) -> Any:
        if self._difficulty is not None:
            return self._difficulty
        else:
            return self._underlay.get_difficulty()

    def get_gaslimit(self) -> Any:
        if self._gaslimit is not None:
            return self._gaslimit
        else:
            return self._underlay.get_gaslimit()

    def get_coinbase(self) -> Any:
        if self._coinbase is not None:
            return self._coinbase
        else:
            return self._underlay.get_coinbase()

    def delete_account(self, address: int):
        self._nonce[address] = DefaultWorldState().get_nonce(address)
        self._balance[address] = DefaultWorldState().get_balance(address)
        self._storage[address] = DefaultWorldState().get_storage(address)
        self._code[address] = DefaultWorldState().get_code(address)
        self._deleted_accounts.add(address)

    def set_nonce(self, address: int, value: Any):
        self._nonce[address] = value
        self._deleted_accounts.discard(address)

    def set_balance(self, address: int, value: Any):
        self._balance[address] = value
        self._deleted_accounts.discard(address)

    def set_storage_data(self, address: int, offset: int, value: Any):
        self._storage.setdefault(address, {})[offset] = value
        self._deleted_accounts.discard(address)

    def set_code(self, address: int, code: Any):
        self._code[address] = code

    def set_blocknumber(self, value: Any):
        self._blocknumber = value

    def set_timestamp(self, value: Any):
        self._timestamp = value

    def set_difficulty(self, value: Any):
        self._difficulty = value

    def set_gaslimit(self, value: Any):
        self._gaslimit = value

    def set_coinbase(self, value: Any):
        self._coinbase = value
