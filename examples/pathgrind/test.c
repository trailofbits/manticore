#include <stdio.h>
#include <stdlib.h>
#include <fcntl.h>
#include <unistd.h>
#include <sys/types.h>
#include <unistd.h>


#define ERROR(x)     do { perror(x); exit(-1); } while (0)
#define ASSERT(x, y) do { if (!(x)) { perror(y); exit(-1); } } while (0)


int main(int argc, char *argv[]) {
    char buffer[5] = { 0 };
    int count = 0;
    int fd, i, k;

    if (argc != 2) {
        printf("Usage: %s <file>\n", argv[0]);
        exit(-1);
    }

    fd = open(argv[1], O_RDONLY);
    ASSERT(fd != -1, "open");

    /*if (read(fd, &buffer[i], 4) != 4) {
        ERROR("read");
    }*/
    
    /*for (i = 0; i < 4; i++) {
        if (read(fd, &buffer[i], sizeof(char)) != sizeof(char)) {
            ERROR("read");
        }
    }*/
    
    for (i = 3; i >= 0; i--) {
        k = lseek(fd, i, SEEK_SET);
        ASSERT(k != -1, "lseek");
        
        k = read(fd, &buffer[i], sizeof(char));
        ASSERT(k == sizeof(char), "read");
    }

    if (buffer[0] == 'b') count++;
    if (buffer[1] == 'a') count++;
    if (buffer[2] == 'd') count++;
    if (buffer[3] == '!') count++;

    if (count == 4) {
        printf("ok\n");
    }

    return 0;
}
