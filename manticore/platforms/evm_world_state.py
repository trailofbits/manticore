import logging
from abc import ABC, abstractmethod
from eth_typing import ChecksumAddress, URI
from io import TextIOBase
from typing import Dict, Optional, Set, Union
from urllib.parse import ParseResult, urlparse
from web3 import Web3
from ..core.smtlib import Array, BitVec, BitVecConstant, BitVecITE, BitVecZeroExtend, ConstraintSet
from ..ethereum.state import State
from ..exceptions import EthereumError

logger = logging.getLogger(__name__)


# sam.moelius: map records which (symbolic) offsets have been written to.  data holds the values
# written.


class Storage:
    def __init__(self, constraints: ConstraintSet, address: int):
        self.constraints = constraints
        self.warned = False
        self.map = constraints.new_array(
            index_bits=256,
            value_bits=1,
            name=f"STORAGE_MAP_{address:x}",
            avoid_collisions=True,
            default=0,
        )
        self.data = constraints.new_array(
            index_bits=256,
            value_bits=256,
            name=f"STORAGE_DATA_{address:x}",
            avoid_collisions=True,
            default=0,
        )
        self.dirty = False

    def set(self, offset: Union[int, BitVec], value: Union[int, BitVec]):
        self.map[offset] = 1
        self.data[offset] = value
        self.dirty = True

    def dump(self, stream: TextIOBase, state: State):
        concrete_indexes = set()
        for sindex in self.map.written:
            concrete_indexes.add(state.solve_one(sindex, constrain=True))

        for index in concrete_indexes:
            stream.write(
                f"storage[{index:x}] = {state.solve_one(self.data[index], constrain=True):x}"
            )

    @staticmethod
    def from_dict(constraints: ConstraintSet, address: int, items: Dict[int, int]) -> "Storage":
        storage = Storage(constraints, address)
        for key, value in items.items():
            storage.set(key, value)
        return storage


####################################################################################################


class WorldState:
    @abstractmethod
    def is_remote(self) -> bool:
        pass

    @abstractmethod
    def accounts(self) -> Set[int]:
        pass

    @abstractmethod
    def get_nonce(self, address: int) -> Union[int, BitVec]:
        pass

    @abstractmethod
    def get_balance(self, address: int) -> Union[int, BitVec]:
        pass

    @abstractmethod
    def has_storage(self, address: int) -> bool:
        pass

    @abstractmethod
    def get_storage(self, address: int) -> Optional[Storage]:
        pass

    @abstractmethod
    def get_storage_data(self, address: int, offset: Union[int, BitVec]) -> Union[int, BitVec]:
        pass

    @abstractmethod
    def get_code(self, address: int) -> Union[bytes, Array]:
        pass

    @abstractmethod
    def get_blocknumber(self) -> Union[int, BitVec]:
        pass

    @abstractmethod
    def get_timestamp(self) -> Union[int, BitVec]:
        pass

    @abstractmethod
    def get_difficulty(self) -> Union[int, BitVec]:
        pass

    @abstractmethod
    def get_gaslimit(self) -> Union[int, BitVec]:
        pass

    @abstractmethod
    def get_coinbase(self) -> Union[int, BitVec]:
        pass


####################################################################################################


class DefaultWorldState(WorldState):
    def is_remote(self) -> bool:
        return False

    def accounts(self) -> Set[int]:
        return set()

    def get_nonce(self, address: int) -> int:
        return 0

    def get_balance(self, address: int) -> int:
        return 0

    def has_storage(self, address: int) -> bool:
        return False

    def get_storage(self, address: int) -> Optional[Storage]:
        raise NotImplementedError

    def get_storage_data(self, address: int, offset: Union[int, BitVec]) -> int:
        return 0

    def get_code(self, address: int) -> bytes:
        return bytes()

    def get_blocknumber(self) -> int:
        # assume initial byzantium block
        return 4370000

    def get_timestamp(self) -> int:
        # 1524785992; // Thu Apr 26 23:39:52 UTC 2018
        return 1524785992

    def get_difficulty(self) -> int:
        return 0

    def get_gaslimit(self) -> int:
        return 0

    def get_coinbase(self) -> int:
        return 0


####################################################################################################


class Endpoint:
    def __init__(self, blocknumber: int, warned: bool):
        self.blocknumber = blocknumber
        self.warned = warned


_endpoints: Dict[str, Endpoint] = {}


def _web3_address(address: int) -> ChecksumAddress:
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
        # sam.moelius: Force WebsocketProvider.__init__ to call _get_threaded_loop.  The existing
        # "threaded loop" could be leftover from a fork, in which case it will not work.
        Web3.WebsocketProvider._loop = None
        web3 = Web3(Web3.WebsocketProvider(URI("ws://" + self._url)))
        blocknumber = None
        try:
            blocknumber = web3.eth.blockNumber
        except ConnectionRefusedError as e:
            raise EthereumError("Could not connect to %s: %s" % (self._url, e.args[1]))
        endpoint = _endpoints.get(self._url)
        if endpoint is None:
            endpoint = Endpoint(blocknumber, False)
            _endpoints[self._url] = endpoint
            logger.info("Connected to %s (blocknumber = %d)", self._url, blocknumber)
        if endpoint.blocknumber != blocknumber:
            if not endpoint.warned:
                logger.warning(
                    "%s blocknumber has changed: %d != %d---someone is using the endpoint besides us",
                    self._url,
                    endpoint.blocknumber,
                    blocknumber,
                )
                endpoint.warned = True
        return web3

    def is_remote(self) -> bool:
        return True

    def accounts(self) -> Set[int]:
        raise NotImplementedError

    def get_nonce(self, address: int) -> int:
        return self._web3().eth.getTransactionCount(_web3_address(address))

    def get_balance(self, address: int) -> int:
        return self._web3().eth.getBalance(_web3_address(address))

    def has_storage(self, address: int) -> bool:
        raise NotImplementedError

    def get_storage(self, address) -> Storage:
        raise NotImplementedError

    def get_storage_data(self, address: int, offset: Union[int, BitVec]) -> int:
        if not isinstance(offset, int):
            raise NotImplementedError
        return int.from_bytes(self._web3().eth.getStorageAt(_web3_address(address), offset), "big")

    def get_code(self, address: int) -> bytes:
        return self._web3().eth.getCode(_web3_address(address))

    def get_blocknumber(self) -> int:
        return self._web3().eth.blockNumber

    def get_timestamp(self) -> int:
        return self._web3().eth.getBlock("latest")["timestamp"]

    def get_difficulty(self) -> int:
        return self._web3().eth.getBlock("latest")["difficulty"]

    def get_gaslimit(self) -> int:
        return self._web3().eth.getBlock("latest")["gasLimit"]

    def get_coinbase(self) -> int:
        return int(self._web3().eth.coinbase)


####################################################################################################


class OverlayWorldState(WorldState):
    """
    If we decide to cache results returned from a RemoteWorldState, then they should NOT be cached
    within an overlay.  The reason is that this could affect the results of subsequent operations.
    Consider a call to get_storage_data followed by a call to has_storage.  If nothing was written
    to storage within the overlay, then the call to has_storage will throw an exception.  But if the
    result of the call to get_storage_data was cached in the overlay, then no exception would be
    thrown.
    """
    def __init__(self, underlay: WorldState):
        self._underlay: WorldState = underlay
        self._deleted_accounts: Set[int] = set()
        self._nonce: Dict[int, Union[int, BitVec]] = {}
        self._balance: Dict[int, Union[int, BitVec]] = {}
        self._storage: Dict[int, Storage] = {}
        self._code: Dict[int, Union[bytes, Array]] = {}
        self._blocknumber: Optional[Union[int, BitVec]] = None
        self._timestamp: Optional[Union[int, BitVec]] = None
        self._difficulty: Optional[Union[int, BitVec]] = None
        self._gaslimit: Optional[Union[int, BitVec]] = None
        self._coinbase: Optional[Union[int, BitVec]] = None

    def is_remote(self) -> bool:
        return self._underlay.is_remote()

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
        )

    def get_nonce(self, address: int) -> Union[int, BitVec]:
        if address in self._nonce:
            return self._nonce[address]
        else:
            return self._underlay.get_nonce(address)

    def get_balance(self, address: int) -> Union[int, BitVec]:
        if address in self._balance:
            return self._balance[address]
        else:
            return self._underlay.get_balance(address)

    def has_storage(self, address: int) -> bool:
        dirty = False
        try:
            dirty = self._underlay.has_storage(address)
        except NotImplementedError:
            pass
        storage = self._storage.get(address)
        if storage is not None:
            dirty = dirty or storage.dirty
        return dirty

    def get_storage(self, address: int) -> Optional[Storage]:
        storage = None
        try:
            storage = self._underlay.get_storage(address)
        except NotImplementedError:
            pass
        # sam.moelius: Rightfully, the overlay's storage should be merged into the underlay's
        # storage.  However, this is not currently implemented.
        if storage is not None:
            raise NotImplementedError
        storage = self._storage.get(address)
        return storage

    def get_storage_data(self, address: int, offset: Union[int, BitVec]) -> Union[int, BitVec]:
        value: Union[int, BitVec] = 0
        # sam.moelius: If the account was ever deleted, then ignore the underlay's storage.
        if address not in self._deleted_accounts:
            try:
                value = self._underlay.get_storage_data(address, offset)
            except NotImplementedError:
                pass
        storage = self._storage.get(address)
        if storage is not None:
            if not isinstance(value, BitVec):
                value = BitVecConstant(256, value)
            value = BitVecITE(256, storage.map[offset] != 0, storage.data[offset], value)
        return value

    def get_code(self, address: int) -> Union[bytes, Array]:
        if address in self._code:
            return self._code[address]
        else:
            return self._underlay.get_code(address)

    def get_blocknumber(self) -> Union[int, BitVec]:
        if self._blocknumber is not None:
            return self._blocknumber
        else:
            return self._underlay.get_blocknumber()

    def get_timestamp(self) -> Union[int, BitVec]:
        if self._timestamp is not None:
            return self._timestamp
        else:
            return self._underlay.get_timestamp()

    def get_difficulty(self) -> Union[int, BitVec]:
        if self._difficulty is not None:
            return self._difficulty
        else:
            return self._underlay.get_difficulty()

    def get_gaslimit(self) -> Union[int, BitVec]:
        if self._gaslimit is not None:
            return self._gaslimit
        else:
            return self._underlay.get_gaslimit()

    def get_coinbase(self) -> Union[int, BitVec]:
        if self._coinbase is not None:
            return self._coinbase
        else:
            return self._underlay.get_coinbase()

    def delete_account(self, constraints: ConstraintSet, address: int):
        default_world_state = DefaultWorldState()
        self._nonce[address] = default_world_state.get_nonce(address)
        self._balance[address] = default_world_state.get_balance(address)
        self._storage[address] = Storage(constraints, address)
        self._code[address] = default_world_state.get_code(address)
        self._deleted_accounts.add(address)

    def set_nonce(self, address: int, value: Union[int, BitVec]):
        self._nonce[address] = value

    def set_balance(self, address: int, value: Union[int, BitVec]):
        self._balance[address] = value

    def set_storage(self, address: int, storage: Optional[Storage]):
        if storage is None:
            self._storage.pop(address, None)
        else:
            self._storage[address] = storage

    def set_storage_data(
        self,
        constraints: ConstraintSet,
        address: int,
        offset: Union[int, BitVec],
        value: Union[int, BitVec],
    ):
        storage = self._storage.get(address)
        if storage is None:
            storage = Storage(constraints, address)
            self._storage[address] = storage
        if storage.constraints != constraints:
            if not storage.warned:
                logger.warning("Constraints have changed")
                storage.warned = True
        storage.set(offset, value)

    def set_code(self, address: int, code: Union[bytes, Array]):
        self._code[address] = code

    def set_blocknumber(self, value: Union[int, BitVec]):
        self._blocknumber = value

    def set_timestamp(self, value: Union[int, BitVec]):
        self._timestamp = value

    def set_difficulty(self, value: Union[int, BitVec]):
        self._difficulty = value

    def set_gaslimit(self, value: Union[int, BitVec]):
        self._gaslimit = value

    def set_coinbase(self, value: Union[int, BitVec]):
        self._coinbase = value
