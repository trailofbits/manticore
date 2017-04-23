#define M 6


main(){
int i,count;
unsigned char buffer[M];
read(0, buffer, M);


for (i=0;i <M;i++)
    buffer[i] = buffer[buffer[i]] ^ buffer[i];

count = 0;
for (i=0;i <M;i++)
    count += buffer[i];

if (count == 0x414243)
    printf("You won!");

return 0;
}
