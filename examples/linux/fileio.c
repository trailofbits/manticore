// This example demonstrates reading & writing from files.

#include <errno.h>
#include <stdio.h>
#include <string.h>

int main(int argc, const char **argv) {
    if (argc != 2) {
        fprintf(stderr, "Usage: %s FILE\n", argv[0]);
        return 0;
    }

    const char *fname = argv[1];
    FILE *infile = fopen(fname, "r");
    if (!infile) {
        fprintf(stderr, "Error opening %s: %s\n", fname, strerror(errno));
        return 2;
    }

    char *line;
    size_t line_size;
    ssize_t nread = getline(&line, &line_size, infile);
    if (nread == -1) {
        fprintf(stderr, "Error reading from %s: %s\n", fname, strerror(errno));
        return 3;
    }

    if (strcmp("open sesame", line) == 0) {
        fprintf(stdout, "Welcome!\n");
        return 0;
    } else {
        fprintf(stdout, "Access denied.\n");
        return 4;
    }
}
