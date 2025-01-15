#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define M ((1024*1024)/sizeof(int))

int main(int argc, char * argv[]) {
    int i, j;
    int *m ;
    int n, total;
    if ((argc != 2)||(sscanf(argv[1], "%d%n", &n, &total) < 1)||(strlen(argv[1]) != total)) {
        fprintf(stderr, "Usage: %s N\n", argv[0]);
        return -1;
    }
    
    for(i = 0; i < n; i++) {
        m = (int*) malloc(sizeof(int)*M);
        for(j = 0; j < M; j++) {
            m[j] = j;
        }
    }
    printf("m=%p\n", (void *) m);
    return 0 ;
}
