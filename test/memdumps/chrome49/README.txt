DWORD PTR [ESP]   => pointer to the buffer containing message 
DWORD PTR [[ESP]] => message size
DWORD PTR [ESP+4] => remaining bytes in buffer

WORKSPACE=ws_chrome49

rm -rf ./${WORKSPACE}
mkdir ${WORKSPACE}

python SymbolicExecutor/main.py --policy dicount --procs 4 --offset 16 --workspace ${WORKSPACE} --buffer "DWORD PTR [ESP]" --size "DWORD PTR [[ESP]]" tests/chrome49/10c8_mojo.dmp --log ${WORKSPACE}/manticore.log
