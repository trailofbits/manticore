from manticore.utils.install_helper import ensure_evm_deps

ensure_evm_deps()  # This must be invoked before any imports

from .abi import ABI
from .manticore import ManticoreEVM
