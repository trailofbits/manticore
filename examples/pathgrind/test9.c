#include <stdio.h>
#include <stdlib.h>
#include <fcntl.h>
#include <string.h>
#include <unistd.h>


#define ERROR(x) do { perror(x); exit(-1); } while (0);


void check(const char *buf) {
    int count = 0;
    unsigned int i = 0;
    char c[2] = { 0 };
    int j;

    while (i < strlen(buf)) {
        c[0] = buf[i];
        sscanf(c, "%d", &j);
        count += j;

        if (count == 15) {
              printf("Password ok!\n");
              exit(0);
        }

        ++i;
    }

    printf("Password Incorrect!\n");
}



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
    
    if (read(fd, buf, 4) != 4) {
        ERROR("read");
    }
    
    check(buf);

    return 0;
}
