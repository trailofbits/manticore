#!/bin/bash

# Script to run Manticore tests in a Linux Docker container

# Allow setting solver via environment variable
SOLVER=${MANTICORE_SOLVER:-auto}

echo "Building Docker image for testing (solver: $SOLVER)..."
docker build -f Dockerfile.test -t manticore-test --build-arg MANTICORE_SOLVER=$SOLVER .

if [ $? -ne 0 ]; then
    echo "Failed to build Docker image. Make sure Docker is running."
    exit 1
fi

echo "Running tests in Docker container..."

# Docker run options with solver environment variable
DOCKER_OPTS="--rm -it -e MANTICORE_SOLVER=$SOLVER"

# Run all tests
if [ "$1" == "" ]; then
    echo "Running all tests with solver: $SOLVER"
    docker run $DOCKER_OPTS manticore-test
elif [ "$1" == "ethereum" ]; then
    echo "Running Ethereum tests only with solver: $SOLVER"
    docker run $DOCKER_OPTS manticore-test python -m pytest tests/ethereum/
elif [ "$1" == "native" ]; then
    echo "Running native tests only with solver: $SOLVER"
    docker run $DOCKER_OPTS manticore-test python -m pytest tests/native/
elif [ "$1" == "bash" ]; then
    echo "Starting interactive bash session with solver: $SOLVER"
    docker run $DOCKER_OPTS manticore-test /bin/bash
elif [ "$1" == "check-solvers" ]; then
    echo "Checking available solvers in container..."
    docker run $DOCKER_OPTS manticore-test python scripts/configure_solver.py --check
else
    echo "Running specific test: $@ with solver: $SOLVER"
    docker run $DOCKER_OPTS manticore-test python -m pytest "$@"
fi