#include <stdio.h>
#include <stdint.h>
#include <inttypes.h>


int main ( int argc, char** argv) {
	uint_fast32_t a = 0;
	a--;
	printf("%"PRIuFAST32"\n", a);
	return 0;
}

