#include <stdio.h>
#include <stdlib.h>
#include <fcntl.h>
#include <string.h>
#include <unistd.h>


#define ERROR(x) do { perror(x); exit(-1); } while (0);

const char _itoa_lower_digits[36] = "0123456789abcdefghijklmnopqrstuvwxyz";


char *my_itoa_word(unsigned long value, char *buflim) {
    const char *digits = _itoa_lower_digits;

        *--buflim = digits[value % 10];
    
    return buflim;
}

unsigned int mydiv(unsigned int a, unsigned int b) {
    return a / b;
}

int main(int argc, char *argv[]) {
    char buffer[5] = { 0 };
    /*char tmpuf[16] = { 0 };
    char *p;*/
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
    
    //buffer[3] &= '\x01';
    
    //p = my_itoa_word(*(unsigned int *)buffer, tmpuf + 5);
    //if (strcmp(p, "1") == 0) { // \xd2\x04\x00\x00
    
    if (_itoa_lower_digits[buffer[0] % 10] == '1') {
        printf("ok\n");
    }
    /*if (mydiv(*(unsigned int *)buffer, 13) == 23) {
        printf("ok\n");
    }*/

    return 0;
}
