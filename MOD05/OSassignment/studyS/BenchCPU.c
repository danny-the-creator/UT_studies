#include <stdio.h>
#define N 4200
#define M 1024*1024

int main(int argc, char * argv[]) {
    int i, j;
    long int k=0;
    for(i = 0; i < N; i++) {
        for(j = 0; j < M; j++) {
            k++ ;
        }
    }
    printf("k=%li\n", k);
    return 0 ;
}
