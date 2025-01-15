#include <time.h>
#include <stdio.h>
#include <unistd.h>

int main(int argc, char** argv) {
	time_t a,b;
	a = time(NULL);
	sleep(5);
	b = time(NULL);
	printf("%.0f\n", difftime(b,a));
	return 0;
}
	
