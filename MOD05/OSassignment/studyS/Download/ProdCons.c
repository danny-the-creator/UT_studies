/*  ProdCons.c - Demonstrate a solution to the producer consumer problem
    with a circular buffer, which works correctly with one producer. */

#include <stdio.h>
#include <pthread.h>
#include <semaphore.h>
#include <assert.h>

#define N 4 /* nr of spaces in the circular buffer */
#define M 10 /* nr of items produced and consumed */

sem_t Elements, Spaces;
int B[N];
int In = 0, Out = 0;

void *tprod(void *ptr) {
    int i;
    for(i=0;i<M;i++) { /* Produce(i) */
        sem_wait(&Spaces);
        B[In] = i;
        printf("    B[%d]=%d\n", In, i);
        In = (In + 1) % N;
        sem_post(&Elements);
    }
    pthread_exit(0);
}

void *tcons(void *ptr) {
    int i,k;
    for(i=0;i<M;i++) {
        // sem_wait(&Elements);
        k = B[Out];
        printf("i=%d %d=B[%d]\n", i, k, Out );
        Out = (Out + 1) % N;
        sem_post(&Spaces);
        assert(i==k) ; /* Consume(k) */
    }
    pthread_exit(0);
}

int main(int argc, char * argv[]) {
    int targ[2];
    pthread_t thread[2];
    sem_init(&Elements, 0, 0);
    sem_init(&Spaces, 0, N);
    pthread_create(&thread[0], NULL, &tprod,(void *) &targ[0]);
    pthread_create(&thread[1], NULL, &tcons,(void *) &targ[1]);
    pthread_join(thread[0], NULL);
    pthread_join(thread[1], NULL);
    sem_destroy(&Elements);
    sem_destroy(&Spaces);
    return 0;
}

/*  Please note that the checks on the return value of the system calls
    have been omitted to avoid cluttering the code. However, system calls
    can and will fail, in which case the results are unpredictable. */
