#/bin/bash
set -ex

UDIR=$HOME/unicorn

# Even if unicorn dir was not cached, travis seems to still mkdir it, so check
# if the repo is actually there
if [ ! -f "$UDIR/make.sh" ]; then
    git clone https://github.com/unicorn-engine/unicorn.git $UDIR
    pushd $UDIR
        sudo -H UNICORN_ARCHS="arm x86" ./make.sh
    popd
fi
pushd $UDIR
    sudo -H UNICORN_ARCHS="arm x86" ./make.sh install
popd
pushd $UDIR/bindings/python
    UNICORN_ARCHS="arm x86" pip install --verbose -e .
popd
