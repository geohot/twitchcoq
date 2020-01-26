#include <stdio.h>

int fact(int n) {
	int r = 1;
	int i;
	for (i = 2; i <= n; i++) r *= i;
	return r;
}

int main(void) {
	printf("fact(10) = %d\n", fact(10));
	return 0;
}

