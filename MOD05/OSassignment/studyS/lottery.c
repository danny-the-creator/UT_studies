#include <stdio.h>

int main(int argc, char** argv) {
	char buf[20];
	int won;

	won = 0;
	printf("Enter your name:\n");
	gets(buf);
	if (won) {
		printf("Congratulations %s, you won the lottery!\n", buf);
	} else {
		printf("Sorry %s, you did not win the lottery!\n", buf);
	}
	return 0;
}
