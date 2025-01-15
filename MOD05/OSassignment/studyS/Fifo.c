/*  Fifo.c - Demonstrate the use of a named pipe connecting a parent and a
    child process to transfer a random number.*/

#include <unistd.h>
#include <stdlib.h>
#include <stdio.h>
#include <sys/wait.h>
#include <time.h>
#include <sys/stat.h>
#include <fcntl.h>

int main(int argc, char **argv) {
    if(argc>=2) {
        int r;
        mkfifo(argv[1], 0666) ;
        pid_t pid=fork();
        if(pid== 0) {
            int fd = open(argv[1], O_RDONLY);
            read(fd, &r, sizeof (int));
            printf("child  %d\n", r);
            close(fd);
        } else {
            int fd = open(argv[1], O_WRONLY, 0666);
            srand(time(NULL));
            r = rand();
            printf("parent %d\n", r);
            write(fd, &r, sizeof (int));
            close(fd);
            waitpid(pid,0,0);
        }
        return 0;
    } else {
        printf("usage: %s fifo\n", argv[0]);
        return 1;
    }
}

/*  Please note that the checks on the return value of the system calls
    have been omitted to avoid cluttering the code. However, system calls
    can and will fail, in which case the results are unpredictable. */
