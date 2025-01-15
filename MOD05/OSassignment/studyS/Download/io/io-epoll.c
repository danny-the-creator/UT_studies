#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <sys/epoll.h>
#include <fcntl.h>

#define SIZE 1024
#define _POSIX_C_SOURCE 200809L

#define MAX_EVENTS 10

void readOnce(int fd, char * message) {
	char buf[SIZE];
	ssize_t received = read(fd, buf, SIZE);
	if (received <= 0) {
		perror("read failed");
		exit(1);
	}
	printf("%s: %.*s", message, (int)received, buf);
}

int main(int argc, char** argv) {
	int fdgood = open("good", O_RDONLY);
	int fdbad = open("bad", O_RDONLY);
	int epollfd = epoll_create(2);
	int nfds, i;
	struct epoll_event ev,events[MAX_EVENTS];
	if (epollfd == -1) {
		perror("epoll_create failed");
		return 1;
	}
	ev.events = EPOLLIN;
	ev.data.fd = fdgood;
        if (epoll_ctl(epollfd, EPOLL_CTL_ADD, fdgood, &ev) == -1) {
                perror("epoll_add good");
                return 1;
        }
	ev.events = EPOLLIN;
	ev.data.fd = fdbad;
	if (epoll_ctl(epollfd, EPOLL_CTL_ADD, fdbad, &ev) == -1) {
		perror("epoll_add bad");
		return 1;
	}
	while (1) {
		nfds = epoll_wait(epollfd, events, MAX_EVENTS, -1);
		if (nfds == -1) {
			perror("epoll_wait");
			return 1;
		}
		for (i = 0; i < nfds; i++) {
			if(events[i].data.fd == fdgood) {
				readOnce(fdgood, "message from good");
			} else if (events[i].data.fd == fdbad) {
				readOnce(fdbad, "message from bad");
			}
		}
	}
}
		

