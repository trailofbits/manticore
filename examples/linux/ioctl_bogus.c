// This example demonstrates a particular syscall that fails at runtime.
// Used primarily as a test of Manticore's file-related syscall implementation.

#include <errno.h>
#include <stdio.h>
#include <string.h>
#include <stropts.h>
#include <sys/socket.h>

int main() {
    // try bogus ioctl on a non-open file descriptor
    int rc = ioctl(42, I_FLUSH, FLUSHRW);
    if (rc == -1) {
        fprintf(stderr, "error: %s\n", strerror(errno));
        return 1;
    } else {
        fprintf(stdout, "success!\n");
        return 0;
    }
}
