#include <libcgc.h>
#define message1 "TOKEN found\n"
#define message2 "TOKEN Not fount\n"
#define TOKEN "HATTORIHANZO"
int strcmp(const char* s1, const char* s2)
{
    while(*s1 && (*s1==*s2))
        s1++,s2++;
    return *(const unsigned char*)s1-*(const unsigned char*)s2;
}

int global_int = 0;
int main(void) {
    char local_buffer[32];
    receive(STDIN, &local_buffer, sizeof(local_buffer), NULL);

    if (strcmp(local_buffer, TOKEN) == 0)
         transmit(STDOUT, message1, sizeof(message1)-1, NULL);
    else
         transmit(STDOUT, message2, sizeof(message2)-1, NULL);
    
    return 0;
}
