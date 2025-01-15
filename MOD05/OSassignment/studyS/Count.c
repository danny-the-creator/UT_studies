/*  Count.c - demonstrate the race condition between two threads trying to
    read and increment/decrement the shared varable Ctr. The sempahore
    Mutex can be switched on by giving a command line argument, in which
    case the race condition disappears. */

#include <stdio.h>
#include <pthread.h>
#include <semaphore.h>
#include <assert.h>

typedef	enum { False=0, True=1 } bool ;
#define N 10

sem_t Mutex; /* shared variables */
int Ctr = 0;
bool Switch ;

void *tproc(void *ptr) {
    int i, loc, inc = *((int *) ptr);
    for(i = 1; i <= N; i++) {
        if(Switch) {
            sem_wait(&Mutex);
        }
        loc = Ctr+inc ;
        printf("%d\t%d\n", inc, loc);
	sched_yield();
        Ctr = loc ;
        if(Switch) {
            sem_post(&Mutex);
        }
    }
    pthread_exit(0);
}

int main(int argc, char * argv[]) {
    int targ[2] = {1,-1};
    pthread_t thread[2];
    sem_init(&Mutex, 0, 1);    
    Switch = (argc > 1); /* Mutex semaphore on/off */
    printf("inc\tctr\tSwitch=%s\n", (Switch?"true":"false"));
    pthread_create(&thread[0], NULL, &tproc,(void *) &targ[0]);
    pthread_create(&thread[1], NULL, &tproc,(void *) &targ[1]);
    pthread_join(thread[0], NULL);
    pthread_join(thread[1], NULL);
    sem_destroy(&Mutex);
    assert(Ctr == 0);
    return 0;
}

/*  Please note that the checks on the return value of the system calls
    have been omitted to avoid cluttering the code. However, system calls
    can and will fail, in which case the results are unpredictable. */
