#include <stdio.h>
#include <stdlib.h>
#include <fcntl.h>
#include <string.h>
#include <unistd.h>


#define ERROR(x) do { perror(x); exit(-1); } while (0);


int main(int argc, char *argv[]) {
    char buffer[20] = { 0 };
    //char tmpuf[16] = { 0 };
    char *p;
    int fd;
    int size;

    if (argc != 2) {
        printf("Usage: %s <file>\n", argv[0]);
        exit(-1);
    }

    if ((fd = open(argv[1], O_RDONLY)) == -1) {
        ERROR("open");
    }

    if (read(fd, buffer, 20) != 20) {
        ERROR("read");
    }
    
    p = buffer;
    
    size = *(unsigned int *)p;
    p += sizeof(unsigned int);
    
    if (size > 0) {
        printf("ok\n");
    }
    
    /*if (4 * size 
    
    memcpy(tmpuf, p, size);*/

    return 0;
}
