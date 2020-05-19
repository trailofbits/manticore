"""
This is the Manticore's CLI `manticore` script.
"""
import argparse
import logging
import sys

import pkg_resources

from crytic_compile import is_supported, cryticparser
from .core.manticore import ManticoreBase, set_verbosity
from .ethereum.cli import ethereum_main
from .wasm.cli import wasm_main
from .utils import config, log, install_helper, resources

consts = config.get_group("cli")
consts.add("recursionlimit", default=10000, description="Value to set for Python recursion limit")
consts.add("no-colors", default=True, description="Disable ANSI color escape sequences in output")
consts.add("verbosity", default=1, description="Specify verbosity level [1-4]")


if install_helper.has_native:
    from manticore.native.cli import native_main

def is_eth():
    for arg in sys.argv[1:]:
        if not arg.startswith("-") and (arg.endswith(".sol") or is_supported(arg)):
            return True
    return False


def is_wasm():
    for arg in sys.argv[1:]:
        if not arg.startswith("-") and (arg.endswith(".wasm") or arg.endswith(".wat")):
            return True
    return False


if __name__ == "__main__":
    """
    Dispatches execution into one of Manticore's engines: evm or native or wasm.
    """

    resources.check_disk_usage()
    resources.check_memory_usage()


    if is_eth():
        ethereum_main()
    elif is_wasm():
        wasm_main()
    else:
        install_helper.ensure_native_deps()
        native_main()
