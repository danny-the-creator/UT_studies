#include "loop.h"

#define N 850

/* Burn about M * 10 ms CPU time */
void loop(int M) {
    int i, j, k ;
    for(i = 0; i < M; i++) {
        for(j = 0; j < N; j++) {
            for(k = 0; k < N; k++) {
            }
        }
    }
}
