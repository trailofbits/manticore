#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <unistd.h>
#define LEN 5

int main() {
	char src[LEN];
	char dst[LEN];
	read(0, src, LEN);

	strncpy(dst, src, LEN - 2);
	return 0;	
}
