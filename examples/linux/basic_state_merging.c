/**
 * Symbolic values are read from stdin using standard libc calls.
 * Program compares if two binary packed integers at the input with 0x41.
 *
 * Compile with :
 *   $ gcc -static -Os basic_statemerging.c -o basic_statemerging
 *
 * Analyze it with:
 *   $ python examples/script/basic_statemerging.py examples/linux/basic_statemerging
 *
 *   The Merger plugin used in basic_statemerging.py will find two states with state IDs 2, 4 to be at the same program
 *   location (0x40060d) and merge their CPU states which should only require the value for RDI to be merged.
 *
 * Expected output:
 *  $ python /Users/vaibhav/git_repos/manticore/examples/script/basic_statemerging.py examples/linux/basic_statemerging-Os
      about to load state_id = 0
      loaded state_id = 0 at cpu = 0x4008e0
      about to load state_id = 1
      loaded state_id = 1 at cpu = 0x400604
      about to load state_id = 2
      Merged registers:
      RDI
      at PC = 0x40060d, merge succeeded for state id = 2 and 4
      loaded state_id = 2 at cpu = 0x40060d
      about to load state_id = 3
      loaded state_id = 3 at cpu = 0x400612
 *
*/

#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <stdbool.h>

 int main(int argc, char* argv[], char* envp[]){
    unsigned int cmd1, cmd2;
    unsigned int cmdChanged = 0;

     if (read(0, &cmd1, sizeof(cmd1)) != sizeof(cmd1))
    {
        printf("Error reading stdin!");
        exit(-1);
    }
    if (read(0, &cmd2, sizeof(cmd2)) != sizeof(cmd2))
    {
        printf("Error reading stdin!");
        exit(-1);
    }

     if (cmd1 > 0x41)
    {
        cmdChanged = cmd1 - 0x42;
    }
    if (cmd2 < 0x41)
    {
        cmdChanged = cmd2 + 0x42;
    }

     if (cmdChanged == 0) printf("equal\n");
    else printf("not equal\n");

     return 0;
}