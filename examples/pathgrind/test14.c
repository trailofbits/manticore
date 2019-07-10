#include <stdio.h>
#include <stdlib.h>
#include <fcntl.h>
#include <unistd.h>
#include <sys/types.h>
#include <unistd.h>
#include <string.h>


#define ERROR(x)     do { perror(x); exit(-1); } while (0)
#define ASSERT(x, y) do { if (!(x)) { perror(y); exit(-1); } } while (0)


int main(int argc, char *argv[]) {
    char buffer[4], *p, *q;
    unsigned int size;
    int fd;

    if (argc != 2) {
        printf("Usage: %s <file>\n", argv[0]);
        exit(-1);
    }

    ASSERT((fd = open(argv[1], O_RDONLY)) != -1, "open");
    ASSERT(read(fd, buffer, 4) == 4, "read");
    

    size = *(unsigned int *)buffer;
    
    p = malloc(size + 1); /* integer overflow */
    q = malloc(32);
    
    if (p != NULL && size >= 13) {
        p[13] = 'a';
    }
    
    free(p);
    free(q);

    return 0;
}
