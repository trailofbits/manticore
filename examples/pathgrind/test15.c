#include <stdio.h>
#include <stdlib.h>
#include <fcntl.h>
#include <unistd.h>
#include <sys/types.h>
#include <unistd.h>
#include <string.h>


#define ERROR(x)     do { perror(x); exit(-1); } while (0)
#define ASSERT(x, y) do { if (!(x)) { perror(y); exit(-1); } } while (0)

void check(int i) {
    if (i == 0x1234) {
        printf("ok\n");
    } 
}

int main(int argc, char *argv[]) {
    char buffer[4];
    int i;
    volatile int j, k;
    int fd;

    if (argc != 2) {
        printf("Usage: %s <file>\n", argv[0]);
        exit(-1);
    }

    ASSERT((fd = open(argv[1], O_RDONLY)) != -1, "open");
    ASSERT(read(fd, buffer, 4) == 4, "read");
    
    j = 0x1234;
    k = 0x5678;
    i = (buffer[0] == '*') ? j : k; /* mux0x */
    check(i);

    return 0;
}
