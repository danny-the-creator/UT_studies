#include <stdio.h>
#include "loop.h"

int main(int argc, char * argv[]) {
    int i;
    for(i = 0; i < 10; i++) {
        loop(100);
        printf("%d\n", i);
    }
    return 0 ;
}
