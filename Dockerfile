FROM ubuntu:18.04

LABEL name=Manticore
LABEL src="https://github.com/trailofbits/manticore"
LABEL creator="Trail of Bits"
LABEL dockerfile_maintenance=trailofbits

ENV LANG C.UTF-8

RUN export DEBIAN_FRONTEND="noninteractive" && \
    apt-get update && \
    apt-get install -y \
        gpg wget && \
      wget -O - https://apt.kitware.com/keys/kitware-archive-latest.asc 2>/dev/null | gpg --dearmor - | tee /usr/share/keyrings/kitware-archive-keyring.gpg >/dev/null && \
      echo 'deb [signed-by=/usr/share/keyrings/kitware-archive-keyring.gpg] https://apt.kitware.com/ubuntu/ bionic main' | tee /etc/apt/sources.list.d/kitware.list >/dev/null && \
      apt-get update && \
      apt-get -y install python3.7 python3.7-dev python3-pip git wget cmake build-essential pkg-config

# Install solc 0.4.25 and validate it
RUN wget https://github.com/ethereum/solidity/releases/download/v0.4.25/solc-static-linux \
 && chmod +x solc-static-linux \
 && mv solc-static-linux /usr/bin/solc

# If this fails, the solc-static-linux binary has changed while it should not.
RUN [ "c9b268750506b88fe71371100050e9dd1e7edcf8f69da34d1cd09557ecb24580  /usr/bin/solc" = "$(sha256sum /usr/bin/solc)" ]

RUN python3.7 -m pip install -U pip

ADD . /manticore
RUN cd manticore && python3.7 -m pip install .[native]

CMD ["/bin/bash"]
