#include <stdio.h> 
#include <string.h> 
#include <unistd.h>
#define LEN 5

int main() { 
	char str[LEN]; 
	read(0, str, sizeof(str));
	
	int a = strlen(str);
	printf("Length of string is: %d", a); 

	return 0; 
} 
