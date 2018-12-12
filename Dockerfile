FROM ubuntu:18.04
MAINTAINER Trail of Bits <opensource@trailofbits.com>

RUN apt-get -y update && DEBIAN_FRONTEND=noninteractive apt-get -y install python3 python3-pip git

RUN DEBIAN_FRONTEND=noninteractive apt-get install -y build-essential software-properties-common && \
    add-apt-repository -y ppa:ethereum/ethereum && \
    apt-get update && \
    DEBIAN_FRONTEND=noninteractive apt-get install -y solc ethereum

# Install Manticore
ADD . /manticore
RUN cd manticore && pip3 install .[native]
z
CMD ["/bin/bash"]
