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

void gen_swap(int *a, int *b, int r);
int swap(int *x, int *y) {
	int tmp = *x;
	*x = *y;
	*y = tmp;
	return 0;
}

void test_swap() {
	int x = 28;
	int y = 42;
	int r = 0;
	x = mksym_i32();
	y = mksym_i32();
	limit2_i32(&x, 0, 28);
	limit2_i32(&y, 42, 101);
	if (x == y)
		x++;
	r = swap(&x,&y);
	gen_swap(&x,&y,r);
}

void gen_ptrarg(int *x, int res);
int ptrarg(int *x) {
	return *x + 1;
}

void test_ptrarg() {
	int x = mksym_i32();
	limit2_i32(&x,28,42);
	int res = ptrarg(&x);
	gen_ptrarg(&x, res);
}

void gen_ptr2arg(int **x, int res);
int ptr2arg(int **x) {
	return **x + 2;
}

void test_ptr2arg() {
	int x = mksym_i32();
	limit2_i32(&x,101,128);
	int *y = &x;
	int res = ptr2arg(&y);
	gen_ptr2arg(&y, res);
}









