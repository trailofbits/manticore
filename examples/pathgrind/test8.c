#define _BSD_SOURCE
#include <stdio.h>
#include <stdlib.h>
#include <fcntl.h>
#include <unistd.h>
#include <string.h>
#include <sys/socket.h>
#include <netinet/in.h>
#include <arpa/inet.h>


#define ERROR(x) do { perror(x); exit(-1); } while (0);

static char tmp_buffer[128];

char *my_inet_ntoa(char *bytes) {
    snprintf(tmp_buffer, 18, "%d.%d.%d.%d", bytes[0], bytes[1], bytes[2], bytes[3]);

    return tmp_buffer;
}



int main(int argc, char *argv[]) {
    char buffer[20];
    /*char bla[4] = { '\x00' };
    unsigned int size;
    char *addr;*/
    int fd;
    char *p;

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
    
    /*volatile int j = 10;
    if (*(int *)buffer - j == -13) {
        printf("ok\n");
    }
    return 0;*/
    
    
    /*volatile int j = 10;
    if (*(int *)buffer / -j == -13) {
        printf("ok\n");
    }
    return 0;*/
    
    /*volatile int j = 10;
    if (*(int *)buffer - j == -13) {
        printf("ok\n");
    }
    return 0;*/
    
    sprintf(tmp_buffer, "%d", buffer[0]);
    if (strcmp(tmp_buffer, "127") == 0) {
        printf("ok\n");
    }
    return 0;
    
    //p = inet_ntoa(*(struct in_addr *)buffer);
    p = my_inet_ntoa(buffer);
    
    if (strcmp(p, "127.0.0.1") == 0) {
        printf("ok\n");
        
        /*p += sizeof(struct in_addr);
        size = *(int *)p;
        
        p += 4;
        memcpy(bla, p, size);*/
    }

    return 0;
}
