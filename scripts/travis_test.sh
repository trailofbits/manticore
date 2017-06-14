#!/bin/bash
RV=0
cd examples/linux
if make; then
    echo "Successfully built Linux examples"
else
    echo "Failed to build Linux examples"
    RV=1
fi
cd ../..

coverage erase
coverage run -m unittest discover tests/ 2>&1 >/dev/null | tee travis_tests.log
DID_OK=$(tail -n1 travis_tests.log)
if [[ "${DID_OK}" == OK* ]]
then
    echo "All functionality tests passed :)"
else
    echo "Some functionality tests failed :("
    RV=1
fi

measure_cov() {
    local PYFILE=${1}
    echo "Measuring coverage for ${PYFILE}"
    local HAS_COV=$(coverage report --include ${PYFILE} | tail -n1 | grep -o 'No data to report')
    if [ "${HAS_COV}" = "No data to report" ]
    then
        echo "    FAIL: No coverage for ${PYFILE}"
        RV=1
        return
    fi
    
    local COV_AMT=$(coverage report --include=${PYFILE} | tail -n1 | sed "s/.* \([0-9]*\)%/\1/g")
    if [ "${COV_AMT}" -gt "${2}" ]
    then
        echo "    PASS: coverage for ${PYFILE} at ${COV_AMT}%"
    else
        echo "    FAIL: coverage for ${PYFILE} at ${COV_AMT}%"
        RV=1
    fi
}

#coverage report
echo "Measuring code coverage..."
measure_cov "manticore/core/smtlib/*" 80
measure_cov "manticore/core/cpu/x86.py" 50
measure_cov "manticore/core/memory.py" 85

exit ${RV}
