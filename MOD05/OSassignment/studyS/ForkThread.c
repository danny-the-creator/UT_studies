/*  ForkThread.c - Demonstrate how threads and processes interact. */

#include <stdio.h>
#include <stdlib.h>
#include <pthread.h>
#include <unistd.h>

void * tproc(void *arg) {
    static char *argv[]={"echo","Foo",NULL};
    fflush(stdout);
    execv("/bin/echo",argv);
    exit(127); /* only if execv fails */
}

int main(int argc, char *argv[]) {
    int targ = 0;
    pthread_t tid;
    pthread_create(&tid, NULL, &tproc, &targ);
    printf("%s\n", argv[0]);
    pthread_join(tid,NULL);
    return 0;
}

/*  Please note that the checks on the return value of the system calls
    have been omitted to avoid cluttering the code. However, system calls
    can and will fail, in which case the results are unpredictable. */
