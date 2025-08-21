FROM ubuntu:20.04

LABEL name=Manticore
LABEL src="https://github.com/trailofbits/manticore"
LABEL creator="Trail of Bits"
LABEL dockerfile_maintenance=trailofbits

ENV LANG=C.UTF-8

RUN apt-get -y update && DEBIAN_FRONTEND=noninteractive apt-get -y install python3 python3-dev python3-pip git wget

# Install solc - architecture aware
# For x86_64: use the original binary that was validated
# For other architectures: skip solc installation (users can install via solc-select if needed)
RUN ARCH=$(uname -m) && \
    if [ "$ARCH" = "x86_64" ]; then \
        wget https://github.com/ethereum/solidity/releases/download/v0.4.25/solc-static-linux && \
        chmod +x solc-static-linux && \
        mv solc-static-linux /usr/bin/solc && \
        # Validate the binary hasn't changed \
        [ "c9b268750506b88fe71371100050e9dd1e7edcf8f69da34d1cd09557ecb24580  /usr/bin/solc" = "$(sha256sum /usr/bin/solc)" ]; \
    else \
        echo "Note: Solidity compiler not installed for $ARCH. Install manually if needed."; \
    fi

# Install Z3 solver (available on most architectures via apt)
RUN DEBIAN_FRONTEND=noninteractive apt-get -y install z3 && \
    apt-get clean && \
    rm -rf /var/lib/apt/lists/*

RUN python3 -m pip install -U pip

ADD . /manticore
RUN cd manticore && python3 -m pip install .[native]

CMD ["/bin/bash"]