#include <stdio.h>
#include <stdlib.h>
#include <fcntl.h>
#include <unistd.h>


#define ERROR(x) do { perror(x); exit(-1); } while (0);


int main(int argc, char *argv[]) {
    char buffer[5] = { 0 };
    int fd;

    if (argc != 2) {
        printf("Usage: %s <file>\n", argv[0]);
        exit(-1);
    }

    if ((fd = open(argv[1], O_RDONLY)) == -1) {
        ERROR("open");
    }

    if (read(fd, buffer, 4) != 4) {
        ERROR("read");
    }
    
    if (*(int *)buffer == 0x64616221) {
        printf("ok\n");
    }
    else {
        //printf("%x\n", *(int *)buffer);
    }

    return 0;
}
