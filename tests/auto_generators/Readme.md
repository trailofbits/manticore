Auto unittest generation
------------------------

1) You need a Linux program that exercises a set of interesting instructions.
For instance try `make` in examples/linux.

2) Run the tracer on your program. It is a gdb wrapper that will execute the program step by step
printing pre/pos information on each instruction:

```
python make_dump.py ../../examples/linux/nostdlib32 > mytest.dump
```
(Several dumps can be concatenated together)

3) Generate the actual python unittest based on the dump.
```
python make_tests.py mytest.dump > SymbolicExecutor/tests/test_example.py
```
This will get up to 1000 testcases for the same mnemonic in the dump.

4) Run the test:
```
python -m unittest -c test_example
```
