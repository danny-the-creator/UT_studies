#include <stdio.h>
#include <unistd.h>

#include <sys/types.h>
#include <sys/stat.h>
#include <fcntl.h>

#define BUFSIZE 4096


int main(int argc, char** argv) {
	int fh;

	char buf[BUFSIZE];
	ssize_t total = 1;
	ssize_t t = 1;
	if (argc != 2) {
		printf("usage: %s <filename>\n", argv[0]);
		return 1;
	}
	fh = open(argv[1], O_RDONLY);
	if (fh == -1) {
		printf("failed to open %s\n", argv[1]);
		return 1;
	}
	if (read(fh, buf, 1) != 1) {
		printf("failed to read the first byte of %s\n", argv[1]);
		return 1;
	}
	printf("Remove the USB thumb drive now!\n");
	for (int i = 0; i < 10; i++) {
		sleep(1);
		printf("%d\n", 9-i);
	}
	while (t > 0) {
		t = read(fh, buf, BUFSIZE);
		if (t > 0) {
			total += t;
		}
	}
	printf("Read %zd bytes from the file!\n", total);
	return 0;
}

