# Manticore Examples

## Quickstart

Install and try Manticore in a few shell commands:

```bash
# Install system dependencies
sudo apt-get update && sudo apt-get install python3 python3-dev python3-pip -y

# Install Manticore and its dependencies
sudo pip3 install manticore[native]

# Download the examples
git clone https://github.com/trailofbits/manticore.git && cd manticore/examples/linux

# Build the examples
make

# Use the Manticore CLI
manticore basic
cat mcore_*/*0.stdin | ./basic
cat mcore_*/*1.stdin | ./basic

# Use the Manticore API
cd ../script
python3 count_instructions.py ../linux/helloworld
```

You can also use Docker to quickly install and try Manticore:

```bash
# Run container with a shared examples/ directory
# Note that `--rm` will make the container be deleted if you exit it
# (if you want to persist data from the container, use docker volumes)
# (we need to increase maximum stack size, so we use ulimit for that)
$ docker run --rm -it --ulimit stack=100000000:100000000 trailofbits/manticore bash

# Change to examples directory
manticore@8d456f662d0f:~$ cd manticore/examples/linux/

# Build the examples
manticore@8d456f662d0f:~/manticore/examples/linux$ make

# Use the Manticore CLI
manticore@8d456f662d0f:~/manticore/examples/linux$ manticore basic


manticore@8d456f662d0f:~/manticore/examples/linux$ cat mcore_*/*0.stdin | ./basic
manticore@8d456f662d0f:~/manticore/examples/linux$ cat mcore_*/*1.stdin | ./basic

# Use the Manticore API
manticore@8d456f662d0f:~/manticore/examples/linux$ cd ../script
manticore@8d456f662d0f:~/manticore/examples/script$ python3 count_instructions.py ../linux/helloworld
```