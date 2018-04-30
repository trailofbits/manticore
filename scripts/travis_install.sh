#!/usr/bin/env bash

function install_solc {
    sudo wget -O /usr/bin/solc https://github.com/ethereum/solidity/releases/download/v0.4.19/solc-static-linux
    sudo chmod +x /usr/bin/solc
}

install_solc
: ${PIP:="pip3"}

$PIP install -U pip
$PIP uninstall -y Manticore || echo "Manticore not cached"  # uninstall any old, cached Manticore
$PIP install --no-binary keystone-engine -e .[dev]  # ks can have pip install issues