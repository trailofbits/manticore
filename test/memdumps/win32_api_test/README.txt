Buffer: DWORD PTR [ DWORD PTR [EBP+0x0C] ]
Length: 18

No ignore APIs:
python SymbolicExecutor/main.py --offset 0 --workspace w32api --buffer "DWORD PTR [ DWORD PTR [EBP+0x0C] ]" --size "0x12" tests/win32_api_test/win32_api_test.dmp

Ignore APIs:
python SymbolicExecutor/main.py --offset 0 --workspace w32api --buffer "DWORD PTR [ DWORD PTR [EBP+0x0C] ]" --size "0x12" tests/win32_api_test/win32_api_test.dmp --names tests/win32_api_test/api_names.txt --log w32api/manticore.log


APIs:
KERNELBASE!WriteFile: 75627525 
kernel32!WriteFile: 756c1400

