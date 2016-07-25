#include "built-in.h"
#include "sym-limits.h"

int ptr_helper2(int **z) {
	if (**z == 42)
		return 4;
	else return
		**z;
}

int ptr_helper(int *y) {
	int **z = &y;
	if (*y == 28)
		return 2;
	else
		return ptr_helper2(&y);
}

void gen_ptr(int x, int r);
int ptr(int x) {
	return ptr_helper(&x);
}

void test_1() {
	int a = 0, r = 0;
	a = mksym_i32();
	r = ptr(a);
	gen_ptr(a,r);
}
