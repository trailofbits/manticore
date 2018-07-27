#!/usr/bin/env bash

function install_solc {
    sudo wget -O /usr/bin/solc https://github.com/ethereum/solidity/releases/download/v0.4.19/solc-static-linux
    sudo chmod +x /usr/bin/solc
}

install_solc

pip install -U pip
pip uninstall -y Manticore || echo "Manticore not cached"  # uninstall any old, cached Manticore

# We only need to install keystone if we're just running regular tests
EXTRAS="dev-noks"
if [ "$1" = "tests" ]; then
    EXTRAS="dev"
fi

pip install --no-binary keystone-engine -e .[$EXTRAS]  # ks can have pip install issues

