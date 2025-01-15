/*  CountSave.c - demonstrate the race condition between two threads trying to
    read and increment/decrement the shared varable Ctr. The sempahore
    Mutex can be switched on by giving a command line argument, in which
    case the race condition disappears. */

#include <stdio.h>
#include <pthread.h>
#include <semaphore.h>
typedef	enum { False=0, True=1 } bool ;
#define N 10

sem_t Mutex; /* shared variables */
int Ctr = 0;
bool Switch ;
int save[2*N];

void *tproc(void *ptr) {
    int i, loc, arg = *((int *) ptr);
    for(i = 0; i < N; i++) {
        if(Switch) {
            sem_wait(&Mutex);
        }
        loc = Ctr+1 ;
        save[N*arg+i] = loc ;
	sched_yield();
        Ctr = loc ;
        if(Switch) {
            sem_post(&Mutex);
        }
    }
    pthread_exit(0);
}

bool check_one( int i ) {
    int k;
    for(k = 0; k < 2*N; k++) {
        if( save[k] == i ) {
            return True ;
         }
    }
    return False;
}

bool check_all() {
    int i ;
    for(i = 1; i <= 2*N; i++) {
        if( ! check_one ( i ) ) {
            return False ;
        }
    }
    return True ;
}

int main(int argc, char * argv[]) {
    int i, targ[2] = {0,1};
    pthread_t thread[2];
    sem_init(&Mutex, 0, 1);    
    Switch = (argc > 1); /* Mutex semaphore on/off */
    pthread_create(&thread[0], NULL, &tproc,(void *) &targ[0]);
    pthread_create(&thread[1], NULL, &tproc,(void *) &targ[1]);
    pthread_join(thread[0], NULL);
    pthread_join(thread[1], NULL);
    sem_destroy(&Mutex);
    if( ! check_all( ) ) {
        printf("Switch=%s\n", (Switch?"true":"false"));
        printf("Error:");
        for(i = 0; i < 2*N; i++) {
            printf("%4d", save[i]);
        }
        printf("\n");
    }
    return 0;
}

/*  Please note that the checks on the return value of the system calls
    have been omitted to avoid cluttering the code. However, system calls
    can and will fail, in which case the results are unpredictable. */
