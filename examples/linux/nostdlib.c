/* Minimal toy example with some input output no stdlib
 * Symbolic values are read from stdin using int80 or syscall. The program has 2 possible paths
 * 
 * Compile with :
 *   $ gcc -fno-builtin -static -nostdlib -m32  -fomit-frame-pointer  toy001.c  -o toy001
 * 
 * Analyze it with:
 *   $ python system.py --sym stdin examples/toy001-nostdlib
*/


/* Linux takes system call arguments in registers:
        syscall number  %eax         call-clobbered
        arg 1           %ebx         call-saved
        arg 2           %ecx         call-clobbered
        arg 3           %edx         call-clobbered
        arg 4           %esi         call-saved
        arg 5           %edi         call-saved
        arg 6           %ebp         call-saved
*/
static inline
int syscall(int syscall_number, int arg1, int arg2, int arg3)  {
    int ret;
    asm volatile (
        "pushl %%ebp\n\t"
        "movl %1, %%eax\n\t"
        "movl %2, %%eax\n\t"
        "movl %3, %%ebx\n\t"
        "movl %4, %%ecx\n\t"
        //"movl %4, %%edx\n\t"
        "int $0x80\n\t"
        "popl %%ebp\n\t"
        : "=a"(ret)
        : "g"(syscall_number), "g"(arg1), "g"(arg2), "g"(arg3)
        : "%ebx", "%ecx", "%edx", "%esi", "%edi"
    );
return ret;
}

int write(int fd, void* buffer, unsigned int size){
    return syscall(4, fd, (int) buffer, size);
}

int read(int fd, void* buffer, unsigned int size){
    return syscall(3, fd, (int) buffer, size);
}

int exit(int errorlevel){
    return syscall(1, errorlevel,0,0);
}

void _start(){
    unsigned char cmd;
    read(0,&cmd,1);

    if (cmd > 0x7f)
    {
        write(1, "Message: It is greater than 0x7f\n", 33);
    }
    else 
    {
        write(1, "Message: It is smaller or equal than 0x7f\n", 42);
    }

    exit(0);
}


