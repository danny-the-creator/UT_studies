/*  Asymmetric.c - Demonstrate the semaphore solution to the dining
    philosophers problem. Philosopher N-1 waits for the right for first,
    whereas the other philosophers wait for the left fork first. */

#include <stdio.h>
#include <pthread.h>
#include <semaphore.h>

#define N 5 /* Number of times each philosopher tries to eat */
#define P 3 /* Number of philosophers */

sem_t Fork[P];

void *tphilosopher(void *ptr) {
    int i, k = *((int *) ptr);
    for(i = 1; i <= N; i++) {
        printf("%*cThink %d %d\n", k*4, ' ', k, i);
        if( k == P-1 ) {
            sem_wait(&Fork[(k+1) % P]) ;
            sem_wait(&Fork[k]) ;
        } else {
            sem_wait(&Fork[k]) ;
            sem_wait(&Fork[(k+1) % P]) ;
        }
        printf("%*cEat %d %d\n", k*4, ' ', k, i);
        sem_post(&Fork[k]) ;
        sem_post(&Fork[(k+1) % P]) ;
    }
    pthread_exit(0);
}

int main(int argc, char * argv[]) {
    int i, targ[P];
    pthread_t thread[P];
    for(i=0;i<P;i++) {
        sem_init(&Fork[i], 0, 1);    
    }
    for(i=0;i<P;i++) {
        targ[i] = i;
        pthread_create(&thread[i], NULL, &tphilosopher,(void *) &targ[i]);
    }
    for(i=0;i<P;i++) {
        pthread_join(thread[i], NULL);
    }
    for(i=0;i<P;i++) {
        sem_destroy(&Fork[i]);
    }
    return 0;
}

/*  Please note that the checks on the return value of the system calls
    have been omitted to avoid cluttering the code. However, system calls
    can and will fail, in which case the results are unpredictable. */
