How to run the test:


No ignore APIs:
python SymbolicExecutor/main.py --offset 0 --workspace test --buffer "DWORD PTR [EBP-0x28]" --size "0x20" tests/ignore_an_api/ignore_an_api.dmp

Ignore APIs:
python SymbolicExecutor/main.py --offset 0 --workspace test --buffer "DWORD PTR [EBP-0x28]" --size "0x20" tests/ignore_an_api/ignore_an_api.dmp --names tests/ignore_an_api/api_names.txt --log tests/manticore.log


APIs to Ignore:
KERNELBASE!CloseHandle: 75438d60

Optional APIs (can ignore or not ignore):
KERNELBASE!GetStdHandle: 75445190

76edc6b0 stdcall windows.ntdll.RtlFreeHeap
