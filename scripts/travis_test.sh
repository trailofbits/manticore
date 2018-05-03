#!/bin/bash

RV=0

set -o errexit
set -o pipefail

# Run all examples; this assumes PWD is examples/script
run_examples() {
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

pushd examples/linux
make
for example in $(make list); do
    ./$example < /dev/zero > /dev/null
done
echo Built and ran Linux examples
popd

pushd examples/script
run_examples
echo Ran example scripts
popd

coverage erase
coverage run -m unittest discover tests/ 2>&1 >/dev/null | tee travis_tests.log
DID_OK=$(tail -n1 travis_tests.log)
if [[ "${DID_OK}" == OK* ]]
then
    echo "All functionality tests passed :)"
else
    echo "Some functionality tests failed :("
    exit 2
fi

measure_cov() {
    local PYFILE=${1}
    echo "Measuring coverage for ${PYFILE}"
    local HAS_COV=$(coverage report --include ${PYFILE} | tail -n1 | grep -o 'No data to report')
    if [ "${HAS_COV}" = "No data to report" ]
    then
        echo "    FAIL: No coverage for ${PYFILE}"
        return 1
    fi
    
    local COV_AMT=$(coverage report --include=${PYFILE} | tail -n1 | sed "s/.* \([0-9]*\)%/\1/g")
    if [ "${COV_AMT}" -gt "${2}" ]
    then
        echo "    PASS: coverage for ${PYFILE} at ${COV_AMT}%"
    else
        echo "    FAIL: coverage for ${PYFILE} at ${COV_AMT}%"
        return 1
    fi
    return 0
}

#coverage report
echo "Measuring code coverage..."
measure_cov "manticore/core/smtlib/*" 80
measure_cov "manticore/core/cpu/x86.py" 50
measure_cov "manticore/core/memory.py" 85

exit ${RV}
