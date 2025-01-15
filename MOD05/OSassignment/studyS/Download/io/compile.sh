#!/bin/sh
gcc -Wall -Werror -o io-fork io-fork.c
gcc -Wall -Werror -o io-epoll io-epoll.c
gcc -Wall -Werror -o io-thread -pthread io-thread.c

mkfifo good
mkfifo bad
