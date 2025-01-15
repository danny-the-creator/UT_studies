#include <stdio.h>
#include <stdlib.h>
#define N 80
#define M 1024*256

int main(int argc, char * argv[]) {
    int i, j;
    int *m ;
    for(i = 0; i < N; i++) {
        m = (int*) malloc(sizeof(int)*M);
        for(j = 0; j < M; j++) {
            m[j] = j;
        }
    }
    printf("m=%p\n", (void *) m);
    return 0 ;
}
