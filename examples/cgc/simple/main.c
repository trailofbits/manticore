#include <libcgc.h>
#define msg1 "It's a number\n"
#define msg2 "Not a number\n"

int main(void) {
    char local=0;
    receive(STDIN, &local, 1, NULL);

    if (local >= '0')
    {
         if (local <= '9')
             transmit(STDOUT, msg1, sizeof(msg1), NULL);
         else
             transmit(STDOUT, msg2, sizeof(msg2), NULL);
    }
    else
         transmit(STDOUT, msg2, sizeof(msg2), NULL);
    
    return 0;
}
