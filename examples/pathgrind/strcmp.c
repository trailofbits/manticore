#include <stdio.h>
#include <stdlib.h>
#include <fcntl.h>
#include <unistd.h>
#include <string.h>


#define ERROR(x) do { perror(x); exit(-1); } while (0);


int main(int argc, char *argv[]) {
    char buffer[16];
    int fd;

    if (argc != 2) {
        printf("Usage: %s <file>\n", argv[0]);
        exit(-1);
    }

    if ((fd = open(argv[1], O_RDONLY)) == -1)
        ERROR("open");

    if (read(fd, buffer, sizeof(buffer)) != sizeof(buffer))
        ERROR("read");
        
    buffer[sizeof(buffer) - 1] = '\x00';

    if (strcmp(buffer, "Hello world :)") == 0) {
        printf("ok\n");
    }

    return 0;
}
