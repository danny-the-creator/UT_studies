/*  Fork.c - Demonstrate how the fork system call creates a clone of
    the parent process which then executes the echo command. Then waits
    until the child finishes. */

#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <sys/wait.h>

int main(int argc, char *argv[]) {
    pid_t pid=fork();
    printf("%s\n", argv[0]);
    if (pid==0) { /* child process */
        static char *argv[]={"echo","Foo",NULL};
        execv("/bin/echo",argv);
        exit(127); /* only if execv fails */
    } else { /* pid!=0; parent process */
        waitpid(pid,0,0); /* wait for child exit */
    }
    return 0;
}

/*  Please note that the checks on the return value of the system calls
    have been omitted to avoid cluttering the code. However, system calls
    can and will fail, in which case the results are unpredictable. */
