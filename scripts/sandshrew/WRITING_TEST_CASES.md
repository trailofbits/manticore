# Writing Test Cases

Writing a test case is fairly flexible (no APIs), but should adhere to the follow C-pseudocode format seen below. Read the annotated comments to better understand the design choice.

```c
#include <my_lib.h>
#include <benchmark_lib.h>

/* sandshrew will parse out wrapper functions prepended with SANDSHREW_*,
 * and concretely execute them during SE runtime. Wrapper functions must also:
 *
 *  1. Pass output and input through arg1 and arg2 respectively
 *  2. Return `void`.
 */

void SANDSHREW_benchmark_encrypt(out, in, len, ...) {
    benchmark_encrypt(in, len, out);
}

/* Differing libraries will use calling conventions for their primitives, based on design choices made by
 * devs. As long as a wrapper function exists for a primitive being tested, sandshrew will be able to reason
 * parameters through a uniform convention (`out`, `in`, and other args).
 */

void SANDSHREW_my_encrypt(out, in, len) {
     my_encrypt(out, len);
}


int main(int argc, char *argv[])
{
    /* sandshrew passes in symbolic input in argv[1] */
    symbolic_input = argv[1];

    /* get result from a benchmark primitive (ideally should be verified) */
    SANDSHREW_benchmark_encrypt(out1, symbolic_input, 32, /* other args */);

    /* get result from the primitive being tested */
    SANDSHREW_my_encrypt(out2, symbolic_input, 32, /* other args */);

    /* test for equivalence using strcmp
     * NOTE: implementation must use *_cmp and abort for
     * proper Manticore hooking and instrumentation
     */
    if (strcmp(out1, out2) != 0)
        abort();
}
```

### Compiling

Once complete, compile the C file into a binary normally, passing in the appropriate header directories and linker flags.

```
$ gcc -g -m64 -Iinclude -o test1 test.c -llib1 -llib2
$ sandshrew --test test1 --debug
```
