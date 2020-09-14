# Launches all examples; this assumes PWD is examples/script
launch_examples() {
    COVERAGE_RCFILE=$GITHUB_WORKSPACE/.coveragerc
    # concolic assumes presence of ../linux/simpleassert
    echo "Running concolic.py..."
    HW=../linux/helloworld
    coverage run --append ./concolic.py
    if [ $? -ne 0 ]; then
        return 1
    fi

    echo "Running count_instructions.py..."
    coverage run --append ./count_instructions.py $HW |grep -q Executed
    if [ $? -ne 0 ]; then
        return 1
    fi

    echo "Running introduce_symbolic_bytes.py..."
    gcc -static -g src/state_explore.c -o state_explore
    ADDRESS=0x$(objdump -S state_explore | grep -A 1 '((value & 0xff) != 0)' |
            tail -n 1 | sed 's|^\s*||g' | cut -f1 -d:)
    coverage run --append ./introduce_symbolic_bytes.py state_explore $ADDRESS
    if [ $? -ne 0 ]; then
        return 1
    fi

    echo "Running run_simple.py..."
    gcc -x c -static -o hello test_run_simple.c
    coverage run --append ./run_simple.py hello
    if [ $? -ne 0 ]; then
        return 1
    fi

    echo "Running run_hook.py..."
    MAIN_ADDR=$(nm $HW|grep 'T main' | awk '{print "0x"$1}')
    coverage run --append ./run_hook.py $HW $MAIN_ADDR
    if [ $? -ne 0 ]; then
        return 1
    fi

    echo "Running state_control.py..."
    # Straight from the header of state_control.py
    gcc -static -g src/state_explore.c -o state_explore
    SE_ADDR=0x$(objdump -S state_explore | grep -A 1 'value == 0x41' |
               tail -n 1 | sed 's|^\s*||g' | cut -f1 -d:)
    coverage run --append ./state_control.py state_explore $SE_ADDR
    if [ $? -ne 0 ]; then
        return 1
    fi

    return 0
}

make_vmtests(){
    DIR=`pwd`
    if  [ ! -f ethereum_vm/.done ]; then
        echo "Automaking VMTests" `pwd`
        cd ./tests/ && mkdir -p  ethereum_vm/VMTests_concrete && mkdir -p ethereum_vm/VMTests_symbolic
        rm -Rf vmtests; git clone https://github.com/ethereum/tests --depth=1 vmtests
        for i in ./vmtests/BlockchainTests/ValidBlocks/VMTests/*/*json; do python ./auto_generators/make_VMTests.py -f istanbul -i $i -o ethereum_vm/VMTests_concrete; done
        rm ethereum_vm/VMTests_concrete/test_loop*.py #too slow
        rm -rf ./vmtests
        touch ethereum_vm/.done
    fi
    cd $DIR
}

make_wasm_tests(){
    DIR=`pwd`
    if  [ ! -f .wasm_done ]; then
        echo "Automaking WASM Tests" `pwd`
        cd ./tests/wasm
        ./generate_tests.sh
        touch .wasm_done
    fi
    cd $DIR
}

make_wasm_sym_tests(){
    DIR=`pwd`
    if  [ ! -f .wasm_sym_done ]; then
        echo "Automaking Symbolic WASM Tests" `pwd`
        cd ./tests/wasm_sym
        ./generate_symbolic_tests.sh
        touch .wasm_sym_done
    fi
    cd $DIR
}

install_truffle(){
    npm install -g truffle
}

run_truffle_tests(){
    COVERAGE_RCFILE=$GITHUB_WORKSPACE/.coveragerc
    mkdir truffle_tests
    cd truffle_tests
    truffle unbox metacoin
    coverage run -m manticore . --contract MetaCoin --workspace output --exclude-all --evm.oog ignore --evm.txfail optimistic
    # Truffle smoke test. We test if manticore is able to generate states
    # from a truffle project.
    count=$(find output/ -name '*tx' -type f | wc -l)
    if [ "$count" -lt 25 ]; then
        echo "Truffle test failed" `ls output/*tx -l | wc -l` "< 25"
        return 1
    fi
    echo "Truffle test succeded"
    cd ..
    cp truffle_tests/.coverage .
    return 0
}

run_tests_from_dir() {
    DIR=$1
    COVERAGE_RCFILE=$GITHUB_WORKSPACE/.coveragerc
    echo "Running only the tests from 'tests/$DIR' directory"
    pytest --durations=100 --cov=manticore --cov-config=$GITHUB_WORKSPACE/.coveragerc -n auto "tests/$DIR"
    RESULT=$?
    return $RESULT
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
    cp examples/script/.coverage .
    return $RESULT
}

# Test type
case $TEST_TYPE in
    ethereum_vm)
        make_vmtests
        run_tests_from_dir $TEST_TYPE
        ;;
    ethereum_truffle)
        echo "Running truffle test"
        install_truffle
        run_truffle_tests
        ;;
    wasm)
        make_wasm_tests
        run_tests_from_dir $TEST_TYPE
        ;;
    wasm_sym)
        make_wasm_sym_tests ;&  # Fallthrough
    native)                 ;&  # Fallthrough
    ethereum)               ;&  # Fallthrough
    ethereum_bench)         ;&  # Fallthrough
    other)
        run_tests_from_dir $TEST_TYPE
        ;;
    examples)
        run_examples
        ;;
    *)
        echo "Unknown TEST_TYPE: '$TEST_TYPE'"
        exit 3;
        ;;
esac
