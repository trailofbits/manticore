Run manticore on the Linux version of the Palindrome CB

Manticore's API interception skips expensive initiailzation that otherwise takes hours to emulate.


Execute via:

python SymbolicExecutor/main.py --procs 4 --workspace palindrome_test --log palindrome_test/manticore.log tests/linux_palindrome/Palindrome --names tests/linux_palindrome/api_names.txt
