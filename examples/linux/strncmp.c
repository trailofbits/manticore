/* This program will read data from stdin and compare it with a constant string
 * using standard strcmp function as provided by libc.
 *
 *
 * Compile with :
 *   $ gcc -static -Os strncmp.c -o strncmp
 *
 * Analyze it with:
 *  $ manticore strncmp
 *   - By default, Manticore will consider` all input of stdin to be symbolic
 *
 * Expected output:
 * 2017-04-24 16:04:22,261: [30182] MAIN:INFO: Loading program: ['strncmp']
 * 2017-04-24 16:04:22,262: [30182] MAIN:INFO: Workspace: ./mcore__dZkhU
 * 2017-04-24 16:04:30,642: [30232][5] EXECUTOR:INFO: Generating testcase No. 1 for state No.5 - Program finished correctly
 * 2017-04-24 16:04:32,880: [30232][21] EXECUTOR:INFO: Generating testcase No. 2 for state No.21 - Program finished correctly
 * 2017-04-24 16:04:36,698: [30232][27] EXECUTOR:INFO: Generating testcase No. 3 for state No.27 - Program finished correctly
 * 2017-04-24 16:04:41,033: [30232][32] EXECUTOR:INFO: Generating testcase No. 4 for state No.32 - Program finished correctly
 * 2017-04-24 16:04:46,186: [30232][37] EXECUTOR:INFO: Generating testcase No. 5 for state No.37 - Program finished correctly
 * 2017-04-24 16:04:52,103: [30232][39] EXECUTOR:INFO: Generating testcase No. 6 for state No.39 - Program finished correctly
 * 2017-04-24 16:04:59,245: [30232][10] EXECUTOR:INFO: Generating testcase No. 7 for state No.10 - Program finished correctly
 * 2017-04-24 16:05:05,608: [30232][13] EXECUTOR:INFO: Generating testcase No. 8 for state No.13 - Program finished correctly
 *
 * Look at ./mcore__dZkhU for results.
 *  $ head  *.stdout
 *   ==> test_00000001.stdout <==
 *   Message: Not Found!
 * 
 *   ==> test_00000002.stdout <==
 *   Message: Not Found!
 * 
 *   ==> test_00000003.stdout <==
 *   Message: Not Found!
 * 
 *   ==> test_00000004.stdout <==
 *   Message: Not Found!
 * 
 *   ==> test_00000005.stdout <==
 *   Message: ZARAZA!
 * 
 *   ==> test_00000006.stdout <==
 *   Message: Not Found!
 * 
 *   ==> test_00000007.stdout <==
 *   Message: Not Found!
 * 
 *   ==> test_00000008.stdout <==
 *   Message: Not Found!
 *
*/

#include <stdio.h>
#include <stdlib.h>

int main(int argc, char* argv[], char* envp[]){
    char buffer[0x100] = {0};
    unsigned char cmd;

    read(0, buffer, 0x100);

    if (strcmp(buffer, "ZARAZA") == 0 )
    /*if (buffer[0] == 'Z' && \
        buffer[1] == 'A' && \
        buffer[2] == 'R' && \
        buffer[3] == 'A' && \
        buffer[4] == 'Z' && \
        buffer[5] == 'A' && \
        buffer[6] == '\x00')*/
    {
        printf("Message: ZARAZA!\n");
    }
    else 
    {
        printf("Message: Not Found!\n");
    }

return 0;
}


