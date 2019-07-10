#include <stdio.h>
#include <stdlib.h>
#include <fcntl.h>
#include <string.h>
#include <unistd.h>


#define ERROR(x) do { perror(x); exit(-1); } while (0);


int fun(char *buffer) {
    int count = 0;
    volatile int i = 2;

    if (buffer[0] == 'b') count++;
    if (buffer[1] == 'a') count++;
    if (buffer[2] * i == 'd') count++;
    if (buffer[3] == '!') count++;

    return count;
}


int main(int argc, char *argv[]) {
    char *buffer, *buffer1;
    int count = 0;
    int fd;

    if (argc != 2) {
        printf("Usage: %s <file>\n", argv[0]);
        exit(-1);
    }

    if ((fd = open(argv[1], O_RDONLY)) == -1) {
        ERROR("open");
    }

    if ((buffer = malloc(4)) == NULL) {
        ERROR("malloc");
    }

    if ((buffer1 = malloc(4)) == NULL) {
        ERROR("malloc");
    }

    if (read(fd, buffer, 4) != 4) {
        ERROR("read");
    }

    memcpy(buffer1, buffer, 4);

    count = fun(buffer1);

    if (count == 4) {
        printf("ok\n");
    }

    return 0;
}
