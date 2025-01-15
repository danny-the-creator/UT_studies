/*  Pipe.c - Demonstrate the use of an unnamed pipe connecting a parent and a
    child process to transfer a random number.*/

#include <unistd.h>
#include <stdlib.h>
#include <stdio.h>
#include <sys/wait.h>
#include <time.h>

int main(int argc, char **argv) {
    int r;
    int fd[2];
    pipe(fd);
    pid_t pid=fork();
    if(pid== 0) {
        close(fd[1]);
        read(fd[0], &r, sizeof (int));
        printf("child  %d\n", r);
        close(fd[0]);
    } else {
        close(fd[0]);
        srand(time(NULL));
        r = rand();
        printf("parent %d\n", r);
        write(fd[1], &r, sizeof (int));
        close(fd[1]);
        waitpid(pid,0,0);
    }
    return 0;
}

/*  Please note that the checks on the return value of the system calls
    have been omitted to avoid cluttering the code. However, system calls
    can and will fail, in which case the results are unpredictable. */
