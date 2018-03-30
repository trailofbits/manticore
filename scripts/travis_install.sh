#!/usr/bin/env bash

function install_solc {
    sudo wget -O /usr/bin/solc https://github.com/ethereum/solidity/releases/download/v0.4.19/solc-static-linux
    sudo chmod +x /usr/bin/solc
}

install_solc

pip3 install -U pip
pip3 uninstall -y Manticore || echo "Manticore not cached"  # uninstall any old, cached Manticore
pip3 install --no-binary keystone-engine -e .[dev]  # ks can have pip install issues
