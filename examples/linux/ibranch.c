/* The symbolic input is taken from command line argument and it is
 * used as an index in a function pointer table. Analysis should explore 
 * both functions.
 *
* Compile with :
 *   $ gcc -static -Os ibranch.c -o ibranch
 *
 * Analyze it with:
 *   $ manticore ibranch +
 *
 *   - The character + at the argument will be replaced by a free symbolic byte
 *
 * Expected output:
 * $ manticore ibranch +
 * 2017-04-24 12:05:09,089: [13266] MAIN:INFO: Loading program: ['ibranch', '+']
 * 2017-04-24 12:05:09,090: [13266] MAIN:INFO: Workspace: ./mcore_1DLM6g
 * 2017-04-24 12:05:19,750: [13316][0] MEMORY:INFO: Reading 8 bytes from symbolic address <manticore.core.smtlib.expression.BitVecAnd object at 0x7f629e40b590>
 * 2017-04-24 12:05:27,061: [13316][3] EXECUTOR:INFO: Generating testcase No. 1 for state No.3 - Program finished correctly
 * 2017-04-24 12:05:28,577: [13316][5] EXECUTOR:INFO: Generating testcase No. 2 for state No.5 - Program finished correctly
 *
 *  Look at ./mcore_1DLM6g for results, you will find something like this:
 *  $ cat *.stdout
 *  Function g
 *  Function f
 *   - It found two finishing paths and explore both functions. -
 *   
*/

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

void f(){
    printf("Function f\n");
}
void g(){
    printf("Function g\n");
}


int main(int argc, char* argv[], char* envp[]){
    int i;
    void (*funcs[2])( );

    funcs[0] = f;
    funcs[1] = g;

    if (argc > 1)
        funcs[argv[1][0] == 'g']();


return 0;
}


