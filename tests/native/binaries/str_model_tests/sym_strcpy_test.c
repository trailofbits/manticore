#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <unistd.h>
#define LEN 5

int main() {
	char * A = "src or dst is A";
	char * NA = "src or dst is not A";
	char src[LEN];
	char dst[sizeof(src)];
	read(0, src, sizeof(src));

	strcpy(dst, src);
	if (dst[1] == 'A' || src[1] == 'A'){
		printf(A);
	}
	if (dst[1] != 'A' && src[1] != 'A'){
		printf(NA);
	}
	return 0;	
}
