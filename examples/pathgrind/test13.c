#include <stdio.h>
#include <stdlib.h>
#include <fcntl.h>
#include <unistd.h>
#include <sys/types.h>
#include <unistd.h>


#define ERROR(x)     do { perror(x); exit(-1); } while (0)
#define ASSERT(x, y) do { if (!(x)) { perror(y); exit(-1); } } while (0)


int mult(int x) {
    return 2 * x;
}


void test_me(int x, int y) {
    int z = mult(x);
    
    if (z == y) {
        if (y == x + 10) {
            *(unsigned int *)NULL = 0;
        }
    }
}


int main(int argc, char *argv[]) {
    char buffer[8];
    int fd, x, y;

    if (argc != 2) {
        printf("Usage: %s <file>\n", argv[0]);
        exit(-1);
    }

    fd = open(argv[1], O_RDONLY);
    ASSERT(fd != -1, "open");

    ASSERT(read(fd, buffer, 8) == 8, "read");

    x = *(unsigned int *)&buffer[0];
    y = *(unsigned int *)&buffer[4];
    
    test_me(x, y);

    return 0;
}
