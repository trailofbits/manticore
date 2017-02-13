Buffer: 0x00403018
Length: 0x2E

python SymbolicExecutor/main.py --procs 1 --offset 0 --workspace apiint --buffer "0x00403018" --size "0x2E" tests/api_interception/api_interception.dmp --names tests/api_interception/api_names.txt --log apiint/manticore.log
