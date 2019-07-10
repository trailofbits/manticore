#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <fcntl.h>
#include <unistd.h>
#include <sys/types.h>
#include <unistd.h>


#define ERROR(x)     do { perror(x); exit(-1); } while (0)
#define ASSERT(x, y) do { if (!(x)) { perror(y); exit(-1); } } while (0)


int main(int argc, char *argv[]) {
    char *buffer;
    char p[] = "/home/ftp/bin";
    long lSize;
    FILE *fp;

    if (argc != 2) {
        printf("Usage: %s <file>\n", argv[0]);
        exit(-1);
    }

    fp = fopen(argv[1], "rb");
    if(!fp) perror(argv[1]),exit(1);

    fseek(fp,0L,SEEK_END);
    lSize=ftell(fp);
    rewind(fp);

    buffer = calloc(1,lSize+1);
    if( !buffer ) fclose(fp),fputs("memory alloc fails",stderr),exit(1);
    
    if( 1!=fread( buffer , lSize, 1 , fp) )
    fclose(fp),free(buffer),fputs("entire read fails",stderr),exit(1);

    char *sp = strchr(buffer,' ');
    char *r;
    int j;
    
    if(sp == NULL) {
       char *tmp = strchr(buffer,'/');
       j = tmp-buffer;
       r = tmp;
    }
    else {
       char *tmp = strchr(sp,'/');
       j = tmp-sp;
       r = tmp;
    }
    
    if(r!=NULL) {
    
    char exstr[32];
    strcpy(exstr,buffer);
    strcat(exstr,r);
    if(strlen(exstr) > 32)

         if(strchr(exstr,'.'))
		return 0;
	 else ERROR(exstr);
    } 
    /*
    if(r == NULL) ERROR(r);
    else if(strlen(r) + strlen(buffer) > 32)
         return 0;

    char exstr[32];
 
    strcpy(exstr,buffer);
    strcat(exstr,r);
    */  
    fclose(fp);
    free(buffer);
	    
   return 0;
}
