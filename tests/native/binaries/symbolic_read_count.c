// Compiled on Ubuntu 18.04 Manticore Docker image with
//   gcc -static symbolic_read_count.c -o symbolic_read_count

#include <stdio.h>
#include <stdlib.h>

int main(int argc, char **argv) {
  // Need at least one argument
  if (argc != 2) {
    return -1;
  }

  // Just get the char ordinal value
  unsigned int count = argv[1][0];
  if (count > 9) {
    return 0;
  }

  // Yes... this is very unsafe
  char *buf[10];
  int sz = read(0, buf, count);
  if (sz > 0) {
    printf("WIN: Read more than zero data\n");
  }
  return sz;
}
