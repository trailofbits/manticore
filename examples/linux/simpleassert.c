/**
 * Manticore should find 5 paths, one of which should be the `return -1` error
 * path.
 *
 * This code is based on the symbolic execution example in these slides:
 * https://www.cs.umd.edu/~mwh/se-tutorial/symbolic-exec.pdf
 */

#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>

int main(int argc, char* argv[], char* envp[]){
    int a;
    int b;
    int c;

    int x = 0;
    int y = 0;
    int z = 0;

    if (read(0, &a, sizeof(a)) != sizeof(a))
    {
        printf("Error reading stdin!");
        exit(-1);
    }
    if (read(0, &b, sizeof(b)) != sizeof(b))
    {
        printf("Error reading stdin!");
        exit(-1);
    }
    if (read(0, &c, sizeof(c)) != sizeof(c))
    {
        printf("Error reading stdin!");
        exit(-1);
    }

    if (a) {
        x = -2;
    }

    if (b < 5) {
        if (!a && c) {
            y = 1;
        }
        z = 2;
    }

    if (x + y + z == 3) {
        return -1;
    }

    return 0;
}


