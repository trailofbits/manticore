/* This program uses the input from stdin as an index into a 256 bytes long
 * array of booleans (bytes). Only 3 indexes of the array are set to *true*.
 * All remaining array values are false. 
 * Only indexes in the set { 0xfe, 0xfc, 0xfd } may branch to the "Found" part.
 *
 *
 * Compile with :
 *   $ gcc -static -Os sindex.c -o sindex
 *
 * Analyze it with:
 *   $ manticore sindex
 *
 *   - By default, Manticore will consider` all input of stdin to be symbolic
 *
 * Expected output:
 *  $ manticore sindex
 *  2017-04-24 12:16:53,413: [13490] MAIN:INFO: Loading program: ['sindex']
 *  2017-04-24 12:16:53,414: [13490] MAIN:INFO: Workspace: ./mcore_wZWmf_
 *  2017-04-24 12:17:00,455: [13540][0] MEMORY:INFO: Reading 1 bytes from symbolic address <manticore.core.smtlib.expression.BitVecAnd object at 0x7fe811910150>
 *  2017-04-24 12:17:03,303: [13540][3] EXECUTOR:INFO: Generating testcase No. 1 for state No.3 - Program finished correctly
 *  2017-04-24 12:17:04,883: [13540][5] EXECUTOR:INFO: Generating testcase No. 2 for state No.5 - Program finished correctly
 *
 * Look at ./mcore_IJ2sPb for results.
 *  $ ls -1
 *  command.sh
 *  test_00000001.messages
 *  test_00000001.pkl
 *  test_00000001.smt
 *  test_00000001.stderr
 *  test_00000001.stdin
 *  test_00000001.stdout
 *  test_00000001.syscalls
 *  test_00000001.trace
 *  test_00000001.txt
 *  test_00000002.messages
 *  test_00000002.pkl
 *  test_00000002.smt
 *  test_00000002.stderr
 *  test_00000002.stdin
 *  test_00000002.stdout
 *  test_00000002.syscalls
 *  test_00000002.trace
 *  test_00000002.txt
 *  
 *  Note it generated only 2 finishing traces. 
 *  One for the index selecting a false boolean 
 *  $ cat test_00000002.stdout
 *  Message: Not Found!
 *
 *  and one for the index selecting a true value
 *  $ cat test_00000001.stdout
 *  Message: Found!
 *
 *  test_00000001.stdin contains a single solution for it.
 *  $ hexdump test_00000001.stdin 
 *  But there were 3 possible indexes! { 0xfe, 0xfc, 0xfd } !!
 *  The path constraint describing the full set of solutions can 
 *  be found at test_00000001.smt
*/

#include <stdio.h>
#include <stdlib.h>

int main(int argc, char* argv[], char* envp[]){
    char buffer[0x100] = {0};
    unsigned char cmd;

    buffer[0xfe]=1;
    buffer[0xfc]=1;
    buffer[0xfd]=1;
    
    if (read(0, &cmd, sizeof(cmd)) != sizeof(cmd))
    {
        printf("Error reading stdin!");
        exit(-1);
    }

    if (buffer[cmd])
    {
        printf("Message: Found!\n");
    }
    else 
    {
        printf("Message: Not Found!\n");
    }

return 0;
}


