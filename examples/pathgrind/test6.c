#include <stdio.h>
#include <stdlib.h>
#include <fcntl.h>
#include <unistd.h>


#define ERROR(x) do { perror(x); exit(-1); } while (0);


int myatoi(char *p) {
    int i = 0;
    
    while (*p != '\x00' && *p >= '0' && *p <= '9') {
        i *= 10;
        i += *(unsigned char *)p - '0';
        p++;
    }
    
    return i;
}


int main(int argc, char *argv[]) {
    char buffer[10] = { 0 };
    int fd, i;

    if (argc != 2) {
        printf("Usage: %s <file>\n", argv[0]);
        exit(-1);
    }

    if ((fd = open(argv[1], O_RDONLY)) == -1) {
        ERROR("open");
    }

    if (read(fd, buffer, 10) != 10) {
        ERROR("read");
    }
    
    i = atoi(buffer);
    
    if (i == 0x0badc0de) { // 195936478
        printf("ok\n");
    }

    return 0;
}
