// This example demonstrates a particular syscall that fails at runtime.
// Used primarily as a test of Manticore's file-related syscall implementation.

#include <errno.h>
#include <stdio.h>
#include <string.h>
#include <sys/ioctl.h>
#include <sys/socket.h>

// stropts not included in Ubuntu 20.04+
// #include <stropts.h>
#define FLUSHRW		0x03
#define __SID		('S' << 8)
#define I_FLUSH		(__SID | 5)

int main() {
    // try bogus ioctl on a socket
    int sockfd = socket(AF_INET, SOCK_STREAM, 0);
    if (sockfd < 0) {
        fprintf(stderr, "error opening socket: %s\n", strerror(errno));
        return 1;
    }

    int rc = ioctl(sockfd, I_FLUSH, FLUSHRW);
    if (rc == -1) {
        fprintf(stderr, "got expected error calling ioctl: %s\n", strerror(errno));
        return 0;
    } else {
        fprintf(stdout, "unexpectedly succeeded!\n");
        return 2;
    }
}
