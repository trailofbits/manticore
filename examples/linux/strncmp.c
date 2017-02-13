/* Minimal toy example with input output
 *
 * This program will read data from stdin and compare it with a constant string
 * using standard strcmp function.
 *
 * Compile with :
 *   $ gcc toy004-strcmp.c  -o toy004-strcmp
 *
 * Analize it with:
 *   $ python system.py --sym stdin example/toy004-strcmp
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


