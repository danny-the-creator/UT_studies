#include <stdio.h>
#include <stdlib.h>

#define N 1000000

int main(int argc, char** argv) {
        int * array = (int*)malloc(N);
        while(array != NULL) {
                array = (int*)malloc(N);
        }
        printf("cannot allocate any more memory\n");
        return 0;
}

