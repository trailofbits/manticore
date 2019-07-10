#include <stdio.h>
#include <stdlib.h>
#include <fcntl.h>
#include <unistd.h>
#include <string.h>
#include <sys/types.h>
#include <unistd.h>


#define ERROR(x)  do { perror(x); exit(-1); } while (0)

struct picture {
    char name[5];
    int  x;
};


int main(int argc, char *argv[]) {
    struct picture pict;
    int fd, x;
    char c;

    if (argc != 2) {
        printf("Usage: %s <file>\n", argv[0]);
        exit(-1);
    }

    fd = open(argv[1], O_RDONLY);
    if (fd == -1) {
        ERROR("open");
    }
    
    if (read(fd, &pict, sizeof(pict)) != sizeof(pict)) {
        ERROR("read");
    }
    
    x = pict.x;
    
    if (strcmp(pict.name, "foo?") == 0) {
        printf("useless\n");
    }
    else if (strcmp(pict.name, "bar!") == 0) {
        if (x <= 0) x = -x;
        if (x >= 5) x = 4;

        c = pict.name[x];
    }
    else {
        printf("useless\n");
    }

    return 0;
}
