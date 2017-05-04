/* Minimal toy example with some input output no stdlib
 * Symbolic values are read from stdin using int80 or syscall. The program has 2 posible paths
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
int syscall(int syscall_number, ... )  {
    int ret;
    asm volatile (
        "pushl %%ebp\n\t"
        "movl %1, %%eax\n\t"
        "movl %2, %%ebx\n\t"
        "movl %3, %%ecx\n\t"
        "movl %4, %%edx\n\t"
        "movl %5, %%edi\n\t"
        "movl %6, %%esi\n\t"
        "movl %7, %%ebp\n\t"
        "int $0x80\n\t"
        "popl %%ebp\n\t"
        : "=a"(ret)
        : "g"(syscall_number), "g"(*(&syscall_number+1)), "g"(*(&syscall_number+2)), "g"(*(&syscall_number+3)), "g"(*(&syscall_number+4)), "g"(*(&syscall_number+5)), "g"(*(&syscall_number+6))
        : "%ebx", "%ecx", "%edx", "%esi", "%edi"
    );
return ret;
}

int write(int fd, void* buffer, unsigned int size){
    return syscall(4, fd, buffer, size,0,0,0);
}

int read(int fd, void* buffer, unsigned int size){
    return syscall(3, fd, buffer, size,0,0,0);
}

int exit(int errorlevel){
    return syscall(1, errorlevel,0,0,0,0,0);
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


