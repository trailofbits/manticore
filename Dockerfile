FROM ubuntu:16.04
MAINTAINER David Manouchehri

RUN apt-get -y update && \
	DEBIAN_FRONTEND=noninteractive apt-get -y install z3 python-pip git && \
	git clone https://github.com/trailofbits/manticore.git && \
	cd manticore && \
	pip install --no-binary capstone .

RUN useradd -m manticore
USER manticore
WORKDIR /home/manticore
ENV HOME /home/manticore

CMD ["/bin/bash"]
