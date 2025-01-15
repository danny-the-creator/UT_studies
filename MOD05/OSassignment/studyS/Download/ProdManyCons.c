/*  ProdManyCons.c - Demonstrate a solution to the producer consumer
    problem with a circular buffer, which works correctly with more than
    one producer. The semaphore Mutex can be switched on with a command
    line argument to ensure that producers will not interfere with one
    another in the buffer handling. */

#include <stdio.h>
#include <pthread.h>
#include <semaphore.h>
#include <unistd.h>
#include <assert.h>

#define P 5 /* nr of producers */
#define N 4 /* buffer size */
#define M 5 /* nr of items produced and consumed */

sem_t Elements, Spaces, Mutex;
int B[N];
int In = 0, Out = 0;
int Switch;

void *tcons(void *ptr) {
    int i,k,sum=0;
    for(i=0;i<M*P;i++) {
        sem_wait(&Elements);
        k = B[Out];
        printf("%d=B[%d]\n", k, Out);
        Out = (Out + 1) % N;
        sem_post(&Spaces);
        sum += k; /* Consume(k) */
    }
    assert(sum == (P*M-1)*P*M/2);
    pthread_exit(0);
}

void *tprod(void *ptr) {
    int i,k,arg=*((int *) ptr);
    for(i=0;i<M;i++) {
        k = i+arg; /* Produce(k) */
        sem_wait(&Spaces);
        if(Switch) {
            sem_wait(&Mutex);
        }
        B[In] = k;
        printf("%*cB[%d]=%d\n", arg+4,' ',In, k);
        In = (In + 1) % N;
        if(Switch) {
            sem_post(&Mutex);
        }
        sem_post(&Elements);
    }
    pthread_exit(0);
}

int main(int argc, char * argv[]) {
    int i,targ[P+1];
    pthread_t thread[P+1];
    Switch = (argc > 1); /* Mutex semaphore on/off */
    printf("Switch=%s\n", (Switch?"true":"false"));
    sem_init(&Mutex, 0, 1);    
    sem_init(&Elements, 0, 0);    
    sem_init(&Spaces, 0, N);    
    pthread_create(&thread[0], NULL, &tcons,(void *) &targ[0]);
    for(i=1;i<=P;i++) {
        targ[i]=(i-1)*M;
        pthread_create(&thread[i], NULL, &tprod,(void *) &targ[i]);
    }
    for(i=0;i<=P;i++) {
        pthread_join(thread[i], NULL);
    }
    sem_destroy(&Elements);    
    sem_destroy(&Spaces);    
    sem_destroy(&Mutex);    
    return 0;
}

/*  Please note that the checks on the return value of the system calls
    have been omitted to avoid cluttering the code. However, system calls
    can and will fail, in which case the results are unpredictable. */
