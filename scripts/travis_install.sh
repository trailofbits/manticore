#!/usr/bin/env bash

function install_solc {
    sudo wget -O /usr/bin/solc https://github.com/ethereum/solidity/releases/download/v0.4.24/solc-static-linux
    sudo chmod +x /usr/bin/solc
}

function install_mcore {
    pip install -U pip
    pip uninstall -y Manticore || echo "Manticore not cached"  # uninstall any old, cached Manticore


    # We only need to install keystone if we're running tests other than ethereum
    EXTRAS="dev-noks"
    if [ "$1" != "ethereum" ]; then
        EXTRAS="dev"
    fi

    # Unicorn needs python2
    export UNICORN_QEMU_FLAGS="--python=/usr/bin/python"

    pip install -I --no-binary keystone-engine -e .[$EXTRAS]  # ks can have pip install issues
}

function install_cc_env {
    curl -L https://codeclimate.com/downloads/test-reporter/test-reporter-latest-linux-amd64 > ./cc-test-reporter
    chmod +x ./cc-test-reporter

    pip install awscli
}

# install CodeClimate env in all conditions
install_cc_env

if [ "$1" != "env" ]; then
    install_solc
    install_mcore $1
fi
