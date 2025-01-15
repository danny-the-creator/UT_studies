/*  ProcessLayout.c - discover the memory layout of a process */
#include <unistd.h>
#include <stdio.h>
#include <pthread.h>
#include <alloca.h>

#define M 1024*1024
#define N 2
#define B 64

void *tproc(void *ptr) {
    printf("tid=%p stack=%p\n", (void *) pthread_self(), (void *) &ptr);
    fflush(stdout);
    sleep(1);
    pthread_exit(0);
}

char s[B]; /* This is declared at global level to make the initialiser of pmap_argv work */

int main(int argc, char * argv[]) {
    int i ;
    pthread_t thread;
    snprintf(s, B, "%d", getpid());
    printf("pid=%s, tid=%p\n", s, (void *) pthread_self());
    fflush(stdout);
    for(i = 0; i < N; i++) {
       void * p = sbrk(M) ;
       pthread_create(&thread, NULL, &tproc, NULL);
       printf("sbrk %p\n", p);
    }
    pid_t pid=fork();
    if (pid==0) {
        char *pmap_argv[]={"pmap","-x",s,NULL};
        execv("/usr/bin/pmap", pmap_argv);
    }
    sleep(1);
    return 0;
}

/*  Please note that the checks on the return value of the system calls
    have been omitted to avoid cluttering the code. However, system calls
    can and will fail, in which case the results are unpredictable. */
