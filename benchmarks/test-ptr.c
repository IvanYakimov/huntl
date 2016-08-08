#include "built-in.h"
#include "sym-limits.h"
#include <limits.h>

int ptrtoint_helper(int dummy) {
	int c1 = 28;
	char *x1 = c1;
	unsigned long x1_ptr = x1;
	short *x2 = c1;
	unsigned long x2_ptr = x2;
	int *x3 = c1;
	unsigned long x3_ptr = x3;
	long *x4 = c1;
	unsigned long x4_ptr = x4;
	if (x1_ptr == c1 && x2_ptr == c1 && x3_ptr == c1 && x4_ptr == c1)
		return 1;
	else
		return 0;
}
void gen_ptrtoint_helper(int x, int r);
void test_ptrtoint() {
	int a = 28, r = 0;
	//a = mksym_i32();
	limit2_i32(&a, 0, 28);
	r = ptrtoint_helper(a);
	gen_ptrtoint_helper(a,r);
}

void twice_helper(int *x) {
	*x = *x * 2;
}

int twice(int x) {
	twice_helper(&x);
	return x;
}

void gen_twice(int x, int r);

void test_twice() {
	int a = 28;
	a = mksym_i32();
	limit2_i32(&a, 0, 28);
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

void test_swap() {
	int x = 28;
	int y = 42;
	x = mksym_i32();
	y = mksym_i32();
	limit2_i32(&x, 0, 28);
	limit2_i32(&y, 42, 101);
	if (x == y)
		x++;
	int r = swap_tester(x,y);
	gen_swap_tester(x,y,r);
}













