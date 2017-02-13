#/bin/bash
set -ex

Z3_VERSION=z3-4.4.2.0d0d504d6273-x64-ubuntu-14.04

mkdir z3
pushd z3
wget https://s3.amazonaws.com/manticore-z3/${Z3_VERSION}.zip -O z3.zip
unzip z3.zip
sudo cp -v ${Z3_VERSION}/bin/z3 /usr/bin/z3
popd
