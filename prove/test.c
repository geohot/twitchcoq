#include <stdio.h>

int main(int argc, char *argv[]) {
  int i = atoi(argv[1]);
  if (i < 3) {
    printf("hello\n");
  } else {
    printf("world\n");
  }
}

