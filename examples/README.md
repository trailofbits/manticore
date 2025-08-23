# Manticore Examples

## Quickstart

Install and try Manticore in a few shell commands:

```bash
# Install uv (fast Python package manager)
curl -LsSf https://astral.sh/uv/install.sh | sh

# Install Manticore and its dependencies
uv pip install --system "manticore[native]"

# Download the examples
git clone https://github.com/trailofbits/manticore.git && cd manticore/examples/linux

# Build the examples (requires gcc)
make

# Use the Manticore CLI
manticore basic
# Check the generated test cases
cat mcore_*/*0.stdin | ./basic
cat mcore_*/*1.stdin | ./basic

# Use the Manticore API
cd ../script
python count_instructions.py ../linux/helloworld
```

### Alternative: Using pip

If you prefer using pip instead of uv:

```bash
# Create a virtual environment
python3 -m venv mcenv
source mcenv/bin/activate

# Install Manticore
pip install "manticore[native]"

# Continue with the examples as above...
```

### Using Docker

You can also use Docker to quickly install and try Manticore:

```bash
# Run container with increased stack size for symbolic execution
docker run --rm -it --ulimit stack=100000000:100000000 trailofbits/manticore bash

# Inside the container:
cd manticore/examples/linux/

# Build the examples
make

# Run Manticore on an example
manticore basic

# Test the generated inputs
cat mcore_*/*0.stdin | ./basic
cat mcore_*/*1.stdin | ./basic

# Try the Python API
cd ../script
python count_instructions.py ../linux/helloworld
```
