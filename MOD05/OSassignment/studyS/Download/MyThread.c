/* Thread.c */
#include<stdio.h>
#include<pthread.h>
#include<unistd.h>
#define N 50

void* tproc(void *arg) {
    printf("Thread %d\n", *((int *) arg));
    return NULL;
}

int main(int argc, char * argv[]) {
    int i;
    int targ[N];
    pthread_t tid[N];
    for(i = 0; i < N; i++) {
	targ[i] = i*i;
        if(pthread_create(&(tid[i]), NULL, &tproc, &targ[i]) != 0) {
            printf("Can't create thread %d\n", i);
            return 1;
        }
    }
    for(i = 0; i < N; i++) {
        if(pthread_join(tid[i], NULL) != 0) {
            printf("Can't join thread %d\n", i);
        }
    }
    return 0;
}

/*  Please note that the checks on the return value of the system calls
    have been omitted to avoid cluttering the code. However, system calls
    can and will fail, in which case the results are unpredictable. */
