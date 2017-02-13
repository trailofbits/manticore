


main(){
int i,count;
unsigned char buffer[256];
read(0, buffer, 256);


for (i=0;i <256;i++)
    buffer[i] = buffer[buffer[i]] ^ buffer[i];

count = 0;
for (i=0;i <256;i++)
    count += buffer[i];

if (count == 0x414243)
    printf("You won!");

return 0;
}
