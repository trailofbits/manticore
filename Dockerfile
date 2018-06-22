FROM ubuntu:16.04
MAINTAINER JP Smith

RUN apt-get -y update && \
	DEBIAN_FRONTEND=noninteractive apt-get -y install python-pip git && \
	git clone https://github.com/trailofbits/manticore.git && \
	cd manticore && \
	pip install .

RUN apt-get install -y build-essential software-properties-common && \
    add-apt-repository -y ppa:ethereum/ethereum && \
    apt-get update && \
    apt-get install -y solc ethereum

RUN useradd -m manticore
USER manticore
WORKDIR /home/manticore
ENV HOME /home/manticore

CMD ["/bin/bash"]
