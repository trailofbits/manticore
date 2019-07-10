#include <stdio.h>
#include <stdlib.h>
#include <fcntl.h>
#include <string.h>
#include <unistd.h>


#define ERROR(x) do { perror(x); exit(-1); } while (0)


int main(int argc, char *argv[]) {
    char buf[256] = { 0 };
    int fd;

    if (argc != 2) {
        printf("Usage: %s <file>\n", argv[0]);
        exit(-1);
    }
    
    if ((fd = open(argv[1], O_RDONLY)) == -1) {
        ERROR("open");
    }
    
    if (read(fd, buf, 10) != 10) {
        ERROR("read");
    }
    
    if (strlen(buf) == 8) {
        printf("ok !\n");
    }

    return 0;
}
