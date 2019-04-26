# Tutorial

Let's test sandshrew on a simple toy program, where we pit the SMT solver against a hash function, to see if we can solve for a collision. Concolic execution allows analysis to complete, due to the effective concretization of the nondeterministic hash function.

Let's take a look at `examples/test_openssl_md5.c`:

```c
void
SANDSHREW_MD5(unsigned char * output, char * input)
{
    MD5(input, 32, output);
}


int
main(int argc, char *argv[])
{
    unsigned char in[32];

    unsigned char orig_result[16];
    unsigned char user_result[16];

    SANDSHREW_MD5(orig_result, "s0m3_1nput_123");
    SANDSHREW_MD5(user_result, argv[1]);

    /* if equal, we generated a hash collision! */
    if (__strcmp_ssse3(orig_result, user_result) == 0)
        abort();
    return 0;
}
```

This builds the test case binary and executes sandshrew to analyze it while outputting debug information:

```
$ cd tests/ && make test_openssl_md5
$ sandshrew -t test_openssl_md5 --debug
```
