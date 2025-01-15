#include <stdio.h>
#include <unistd.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <fcntl.h>

#define SIZE 1024
#define _POSIX_C_SOURCE 200809L

void readForever(int fd, char * message) {
	char * buf = NULL;
	size_t len = 0;
	ssize_t received;
	FILE * f = fdopen(fd, "r");
	if (f == NULL) {
		perror("could not call fdopen");
		return;
	}
	while (1) {
		received = getline(&buf, &len, f);
		if (received <= 0) {
			perror("Read failed");
			return;
		} else if (len == 0) {
			perror("Nothing to read anymore");
			return;
		} else {
			printf("%s: %s", message, buf);
			if (buf[received-1] != '\n') {
				printf("\n");
			}
			fflush(stdout);
		}
	}
}

int main(int argc, char** argv) {
	int fdgood = open("good", O_RDONLY);
	int fdbad = open("bad", O_RDONLY);
	pid_t pid = fork();
	if (pid == -1) {
		perror("Fork failed");
		return 1;
	}
	if (pid == 0) {
		// Child
		readForever(fdgood, "message from good");
		return 0;
	} else {
		// Parent
		readForever(fdbad, "message from bad");
		return 0;
	}
}
		

