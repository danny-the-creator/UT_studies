#include <stdio.h>
#include <unistd.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <pthread.h>

#define SIZE 1024
#define _POSIX_C_SOURCE 200809L

struct arg {
	int fd;
	char * message;
};

static void * readForever(void * v) {
	struct arg* a = (struct arg*)v;
	int fd;
	char * message;
	fd = a->fd;
	message = a->message;
	char * buf = NULL;
	size_t len = 0;
	ssize_t received;
	FILE * f = fdopen(fd, "r");
	if (f == NULL) {
		perror("could not call fdopen");
		pthread_exit(NULL);
	}
	while (1) {
		received = getline(&buf, &len, f);
		if (received == -1) {
			perror("Read failed");
			pthread_exit(NULL);
		} else if (received == 0) {
			perror("Nothing to read anymore");
			pthread_exit(NULL);
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
	struct arg good;
	struct arg bad;
	good.fd = fdgood;
	bad.fd = fdbad;
	good.message = "message from good";
	bad.message = "message from bad";
	pthread_t threads[2];
	if (pthread_create(&threads[0], NULL, &readForever, (void*) &good)) {
		return 1;
	}
	if (pthread_create(&threads[1], NULL, &readForever, (void*) &bad)) {
		return 1;
	}
	pthread_join(threads[0], NULL);
	pthread_join(threads[1], NULL);
	return 1;
}
		

