#include <stdio.h>
#include <stdlib.h>
#include <fcntl.h>
#include <unistd.h>
#include <string.h>


#define ERROR(x) do { perror(x); exit(-1); } while (0);


void *memcpy_(char *dest, const char *src, size_t n) {
    while (n-- > 0) {
        dest[n] = src[n];
    }
    return dest;
}

int strcmp_(const char *s1, const char *s2) {
    int i = 0;
    
    //printf("**>\n");
    while (s1[i] && s2[i]) {
        if (s1[i] > s2[i]) {
            return 1;
        }
        else if (s1[i] < s2[i]) {
            return -1;
        }
        i++;
    }
    //printf("**<\n");
    
    return 0;
}

void shift(char *buffer, char *buffer2) {
    unsigned int i;
    
    for (i = 0; i < 4; i++) {
        buffer[i] = buffer2[(i + 1) % 4];
    }
}

int main(int argc, char *argv[]) {
    char buffer[5] = { 0 };
    char buffer2[5] = { 0 };
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
    
    memcpy(buffer2, buffer, sizeof(buffer2));
    
    /*if (buffer2[1] == 'a') {
        printf("ok\n");
    }*/
    
    shift(buffer, buffer2);

    if (strncmp(buffer, "bad!", 4) == 0) {
        printf("ok\n");
    }

    return 0;
}
