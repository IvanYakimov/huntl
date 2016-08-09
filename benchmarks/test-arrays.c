#include "built-in.h"
#include "sym-limits.h"
#include <limits.h>

void gen_arr1(int x, int r);
int arr1(int x) {
	int arr[10];
	for (int i = 0; i < 10; ++i) {
		arr[i] = i;
	}
	return arr[0];
}

void test_arr1() {
	int a = 0, r = 0;
	r = arr1(a);
	gen_arr1(a,r);
}
