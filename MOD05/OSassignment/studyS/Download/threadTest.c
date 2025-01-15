#include <stdio.h>
#include <pthread.h>
#include <inttypes.h>

typedef struct {
  uint64_t x;
  uint64_t y;
} coordinates;

const coordinates leftup = {.x = 1, .y = 1};
const coordinates rightdown = {.x = -1, .y = -1};
coordinates current;

void* tproc(void *arg) {
  int i = 1;
  while(1) {
    i = (i+1)&1;
    if (i == 0) {
      current = leftup;
    } else {
      current = rightdown;
    }
  }
}

int main(int argc, char * argv[]) {
  coordinates r;
  pthread_t tid;
  if(pthread_create(&tid, NULL, &tproc, NULL) != 0) {
    printf("Can't create thread\n");
    return 1;
  }
  while (1) {
    r = current;
    if (r.x != r.y) {
      printf("wrong value: %"PRId64", %"PRId64"\n", r.x, r.y);
    }
  }
}
