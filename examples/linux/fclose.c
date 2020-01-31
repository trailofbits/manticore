// This example closes file descriptors 0, 1, and 2 (which correspond to stdin,
// stdout, and stderr in most environments).
//
// This serves as a reduced testcase for what most of the programs in GNU
// coreutils do.  See #1602 and #1604 on GitHub.

#include <stdbool.h>
#include <stdio.h>
#include <string.h>

int main(int argc, char **argv) {
    if (argc >= 2 && strcmp(argv[1], "--close") == 0) {
        fprintf(stdout, "Closing file handles!\n");

        int rc = 0;
        if (fclose(stdin) != 0) {
            rc += 1;
        }
        if (fclose(stdout) != 0) {
            rc += 2;
        }
        if (fclose(stderr) != 0) {
            rc += 4;
        }

        return rc;
    } else {
        fprintf(stdout, "Not doing anything.\n");
        return 0;
    }
}
