/*  ThreadSched.c - Start up N threads, each of which will print the ID of
    the CPU running the thread. If a thread gets moved to another CPU
    this is noted to demonstrate the effect of the scheduler on processor
    utilisation in a multi-core system. With a command line argument
    present all threads are tied to a specific CPU. */

#define _GNU_SOURCE
#include <stdio.h>
#include <pthread.h>

#define N 50 /* Number of threads */
#define M 1000 /* Number of times to reschedule */
typedef enum { False=0, True=1 } bool ;

bool Switch ;

void *tproc(void *ptr) {
    int k, i = *((int *) ptr);
    cpu_set_t cpuset;
    CPU_ZERO(&cpuset);
    CPU_SET(i, &cpuset);
    if( Switch ) {
        pthread_t thread = pthread_self();
        pthread_setaffinity_np(thread, sizeof(cpu_set_t), &cpuset);
    }
    int bgn = sched_getcpu();
    printf("thread %d on CPU %d\n",i,bgn);
    for(k=0;k<M;k++) {
        int now = sched_getcpu();
        if( bgn != now ) {
            printf("thread %d to CPU %d\n",i,now);
            break;
        }
        sched_yield();
    }
    pthread_exit(0);
}

int main(int argc, char * argv[]) {
    int i, targ[N];
    pthread_t thread[N];
    Switch = (argc > 1); 
    printf("Switch %s\n", (Switch ? "On" : "Off" ));
    for(i=0; i < N; i++) {
        targ[i] = i;
        pthread_create(&thread[i], NULL, &tproc,(void *) &targ[i]);
    }
    for(i=0; i < N; i++) {
        pthread_join(thread[i], NULL);
    }
    return 0;
}

/*  Please note that the checks on the return value of the system calls
    have been omitted to avoid cluttering the code. However, system calls
    can and will fail, in which case the results are unpredictable. */
