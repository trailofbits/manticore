/* Simple program that copies data and makes decisions about it.
 * All data is concrete
*/

#include <stdio.h>
#include <stdlib.h>

int main(int argc, char* argv[], char* envp[]){
    unsigned int cmd = argc;
    
    printf("About to compare\n");

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


