FROM ubuntu:18.04

LABEL name=Manticore
LABEL src="https://github.com/trailofbits/manticore"
LABEL creator="Trail of Bits"
LABEL dockerfile_maintenance=trailofbits

RUN apt-get -y update && DEBIAN_FRONTEND=noninteractive apt-get -y install python3 python3-pip git

RUN DEBIAN_FRONTEND=noninteractive apt-get install -y build-essential software-properties-common && \
    add-apt-repository -y ppa:ethereum/ethereum && \
    apt-get update && \
    DEBIAN_FRONTEND=noninteractive apt-get install -y solc ethereum

ADD . /manticore
RUN cd manticore && pip3 install .[native]

CMD ["/bin/bash"]
