// gcc -g -static -o basic basic.c

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


