#include "built-in.h"
#include "sym-limits.h"
#include <limits.h>

void twice_helper(int *x) {
	*x = 2;
}

int twice(int x) {
	twice_helper(&x);
	return x;
}

void gen_twice(int x, int r);

void test_twice() {
	int a = 28;
	int r = twice(a);
	gen_twice(a,r);
}

void swap(int *x, int *y) {
	int tmp = *x;
	*x = *y;
	*y = tmp;
}

void gen_swap_tester(int a, int b, int r);

int swap_tester(int a, int b) {
	int a0 = a;
	int b0 = b;
	swap(&a,&b);
	if (a == b0 && b == a0)
		return 1;
	else
		return 0;
}

void test_1() {
	int x = 28;
	int y = 42;
	//x = mksym_i32();
	//y = mksym_i32();
	//limit2_i32(&x, INT_MIN, INT_MAX);
	//limit2_i32(&y, INT_MIN, INT_MAX);
	if (x == y)
		x++;
	int r = swap_tester(x,y);
	gen_swap_tester(x,y,r);
}













