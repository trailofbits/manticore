#include <libcgc.h>
#define msg1 "Passed"
#define msg2 "Failed"

int check(int value){
    if (value == 0x41424344)
        return 1;
return 0;
}

void parser(){
    size_t rx_bytes;
    int checksum = 0;
    struct {
        char buffer[32];
        char checksum;
    } value;

    if (receive(STDIN, &value, 64 /* sizeof(value)*/, &rx_bytes))
        _terminate(-1);

    for (; rx_bytes > 0; rx_bytes--)
        checksum += value.buffer[rx_bytes-1];
   
    if (value.checksum != checksum)
        _terminate(-2);

    transmit(STDOUT, msg1, sizeof(msg1), NULL);
}
int main(void) {
    int value = 0;
    receive(STDIN, &value, sizeof(value), NULL);

    if (check(value))
        parser();
    else
        transmit(STDOUT, msg2, sizeof(msg2), NULL);
    
    return 0;
}
