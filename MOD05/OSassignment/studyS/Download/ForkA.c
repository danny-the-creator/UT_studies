#include <stdio.h>
#include <unistd.h>
#include <sys/types.h>
#include <sys/wait.h>

int main(int argc, char** argv) {
	int a = 0; pid_t pid = fork();
	if (pid < 0) { return 0; }
	if (pid == 0) { a++;
	} else {
		wait(NULL);
		printf("%d\n", a);
	}
	return 0;
}
