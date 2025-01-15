/*  MesPass.c - Use a message queue at /dev/mqueue/myqueue as a
    communication channel between P producer threads and one consumer
    thread. */

#include <mqueue.h>
#include <fcntl.h> /* O_flags */
#include <stdio.h>
#include <sys/stat.h> /* S_flags */
#include <string.h>
#include <unistd.h>
#include <stdlib.h>
#include <pthread.h>
#include <assert.h>

#define P 3  /* nr of producers */
#define M 64 /* message size */
#define N 4  /* nr of messages */
#define queue_name "/myqueue"

mqd_t my_open(int oflags) {
    mode_t mode = S_IRUSR | S_IWUSR | S_IRGRP | S_IWGRP | S_IROTH | S_IWOTH;
    char *path = queue_name;
    struct mq_attr attr = {0, N, M, 0};
    return mq_open(path,oflags,mode,&attr);
}

void *tprod(void *ptr) {
    int i,arg=*((int *) ptr);
#ifdef NONBLOCK
    mqd_t mqd = my_open(O_WRONLY | O_NONBLOCK);
#else
    mqd_t mqd = my_open(O_WRONLY);
#endif

    char buf[M];
    for(i=0;i<N;i++) {
        snprintf(buf,M,"%d",arg+i);
        printf("%*csend %s\n", arg+4,' ',buf);
        if( mq_send(mqd,buf,strlen(buf)+1,1) != 0 ) {
            printf("send failed\n");
        }
    }
    mq_close(mqd);
    pthread_exit(0);
}

void *tcons(void *ptr) {
    int i,k,sum=0;
    char buf[M];
    mqd_t mqd = my_open(O_RDONLY);
    for(i=0;i<N*P;i++) {
        mq_receive(mqd,buf,M,0);
        k = atoi(buf);
        printf("recv %d\n",k);
        sum += k;
    }
    assert(sum == (P*N-1)*P*N/2);
    mq_close(mqd);
    pthread_exit(0);
}

void ls() {
    struct stat s; 
    char buf[M];
    snprintf(buf,M,"/dev/mqueue%s", queue_name);
    if( stat(buf, &s) == 0 ) {
        printf("%s found\n", buf);
    } else {
        printf("%s not found\n", buf);
    }
}

int main(int argc, char * argv[]) {
    int i,targ[P+1];
    pthread_t thread[P+1];
    mqd_t mqd = my_open(O_RDWR | O_CREAT);
    pthread_create(&thread[0], NULL, &tcons,(void *) &targ[0]);
    ls();
    for(i=1;i<=P;i++) {
        targ[i]=(i-1)*N;
        pthread_create(&thread[i], NULL, &tprod,(void *) &targ[i]);
    }
    for(i=0;i<=P;i++) {
        pthread_join(thread[i], NULL);
    }
    mq_close(mqd);
    mq_unlink(queue_name);
    return 0;
}

/*  Please note that the checks on the return value of the system calls
    have been omitted to avoid cluttering the code. However, system calls
    can and will fail, in which case the results are unpredictable. */
