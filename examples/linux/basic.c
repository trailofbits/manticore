/* Minimal toy example with input output using libc
 * Symbolic values are read from stdin using standar libc calls. 
 *    
 * Compile with :
 *   $ gcc toy002-libc.c -o toy002-libc
 *     
 * Analize it with:
 *   $ python system.py --sym stdin examples/toy002-libc
*/

#include <stdio.h>
#include <stdlib.h>

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
        printf("Message: It is smaller or equal than 0x41\n");
    }

return 0;
}


