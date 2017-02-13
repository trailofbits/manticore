/* Minimal toy example with input outputA
 *
 * This program will use the input from stdin as an index into a 256 bytes long array of bools (bytes)
 * If input is considered symbolic this will exercise a read on a symbolic input.
 * Only indexes in the set { 0xfe, 0xfc, 0xfd } may branch to the "Found" part.
 * 
 * Compile with :
 *   $ gcc toy003-sindex.c -o toy003-sindex
 *
 * Analize it with:
 *   $ python system.py --sym stdin example/toy003-sindex
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


