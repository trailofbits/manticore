#!/bin/bash

RV=0

set -o errexit
set -o pipefail

# Launches all examples; this assumes PWD is examples/script
launch_examples() {
    # concolic assumes presence of ../linux/simpleassert
    echo "Running concolic.py..."
    HW=../linux/helloworld
    python ./concolic.py
    if [ $? -ne 0 ]; then
        return 1
    fi

    echo "Running count_instructions.py..."
    python ./count_instructions.py $HW |grep -q Executed
    if [ $? -ne 0 ]; then
        return 1
    fi

    echo "Running introduce_symbolic_bytes.py..."
    gcc -static -g src/state_explore.c -o state_explore
    ADDRESS=0x$(objdump -S state_explore | grep -A 1 '((value & 0xff) != 0)' |
            tail -n 1 | sed 's|^\s*||g' | cut -f1 -d:)
    python ./introduce_symbolic_bytes.py state_explore $ADDRESS
    if [ $? -ne 0 ]; then
        return 1
    fi

    echo "Running run_simple.py..."
    gcc -x c -static -o hello - <<-EOF
    #include <stdio.h>
    int main(){return 0;}
	EOF
    python ./run_simple.py hello
    if [ $? -ne 0 ]; then
        return 1
    fi

    echo "Running run_hook.py..."
    MAIN_ADDR=$(nm $HW|grep 'T main' | awk '{print "0x"$1}')
    python ./run_hook.py $HW $MAIN_ADDR
    if [ $? -ne 0 ]; then
        return 1
    fi

    echo "Running state_control.py..."
    # Straight from the header of state_control.py
    gcc -static -g src/state_explore.c -o state_explore
    SE_ADDR=0x$(objdump -S state_explore | grep -A 1 'value == 0x41' |
               tail -n 1 | sed 's|^\s*||g' | cut -f1 -d:)
    python ./state_control.py state_explore $SE_ADDR
    if [ $? -ne 0 ]; then
        return 1
    fi

    return 0
}


run_tests_from_dir() {
    DIR=$1
    coverage erase
    coverage run -m unittest discover "tests/$DIR" 2>&1 >/dev/null | tee travis_tests.log
    DID_OK=$(tail -n1 travis_tests.log)
    if [[ "${DID_OK}" != OK* ]]; then
        echo "Some tests failed :("
        return 1
    else
        coverage xml
    fi
}

run_examples() {
    pushd examples/linux
    make
    for example in $(make list); do
        ./$example < /dev/zero > /dev/null
    done
    echo Built and ran Linux examples
    popd

    pushd examples/script
    launch_examples
    RESULT=$?
    echo Ran example scripts
    popd
    return $RESULT
}

# Test type
case $1 in
    native)     ;&  # Fallthrough
    ethereum)   ;&  # Fallthrough
    other)
        echo "Running only the tests from 'tests/$1' directory"
        run_tests_from_dir $1
        RV=$?
        ;;

    examples)
        run_examples
        ;;

    all)
        echo "Running all tests registered in travis_test.sh: examples, native, ethereum, other";

        # Functions should return 0 on success and 1 on failure
        RV=0
        run_tests_from_dir native
        RV=$(($RV + $?))
        run_tests_from_dir ethereum
        RV=$(($RV + $?))
        run_tests_from_dir other
        RV=$(($RV + $?))
        run_examples
        RV=$(($RV + $?))
        ;;

    *)
        echo "Usage: $0 [examples|native|ethereum|other|all]"
        exit 3;
        ;;
esac



exit ${RV}
