#include <stdio.h>
#include <stdlib.h>

int add(int * a, int b) {
	return (*a) + b;
}

int main(int argc, char** argv) {
	int toReduce = -1;
	printf("You passed %d additional arguments\n", add(&toReduce, argc));
	return 0;
}
	
void allocateOnHeap(int n) {
	int * buf = malloc(sizeof(int)*n);
	for (int i = 0; i < n; i++) {
		buf[i] = i;
	}
	free(buf);
}

void allocateOnStack(int n) {
	int * buf = alloca(sizeof(int)*n);
	for (int i = 0; i < n; i++) {
		buf[i] = i;
	}
}