#include <stdio.h>

int add(int a, int b) {
    return a + b;
}

int increment(int a) {
    return add(a, 1);
}

int main(int argc, char** argv) {
    int a = 3;
    printf("%d + 1 = %d\n", a, increment(a));
    return 0;
}
