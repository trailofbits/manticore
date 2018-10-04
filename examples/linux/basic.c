/**
 * Symbolic values are read from stdin using standard libc calls.
 * Program checks if a binary packed integer at the input is 0x41 or less.
 *
 * Compile with :
 *   $ gcc -static -Os basic.c -o basic
 *
 * Analyze it with:
 *   $ manticore basic
 *
 *   - By default, Manticore will consider all input of stdin to be symbolic
 *
 * Expected output:
 *  $ manticore basic
 *  2017-04-22 10:35:52,789: [9309] MAIN:INFO: Loading program: ['basic']
 *  2017-04-22 10:35:52,792: [9309] MAIN:INFO: Workspace: ./mcore_IJ2sPb
 *  2017-04-22 10:36:24,386: [9359][3] EXECUTOR:INFO: Generating testcase No. 1 for state No.3 - Program finished correctly
 *  2017-04-22 10:36:28,452: [9359][5] EXECUTOR:INFO: Generating testcase No. 2 for state No.5 - Program finished correctly
 *
 *  Look at ./mcore_IJ2sPb for results, you will find something like this:
 *   $ hexdump -C test_00000001.stdin 
 *   00000000  00 80 00 20                                       |... |
 *
 *   $ hexdump -C test_00000002.stdin 
 *   00000000  41 00 00 00                                       |A...|
 * 
 *  You can try out the values like this:
 *
 *   $ printf "\x00\x80\x00\x20" | ./basic 
 *    Message: It is greater than 0x41
 *
 *   $ printf "\x41\x00\x00\x00" | ../basic 
 *    Message: It is smaller or equal than 0x41
*/

#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>

int main(int argc, char* argv[], char* envp[]){
    unsigned int cmd;
    
    if (read(0, &cmd, sizeof(cmd)) != sizeof(cmd))
    {
        printf("Error reading stdin!");
        exit(-1);
    }

    if (cmd > 0x41)
    {
        printf("Message: It is greater than 0x41\n");
    }
    else 
    {
        printf("Message: It is less than or equal to 0x41\n");
    }

return 0;
}


