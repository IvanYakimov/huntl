// see http://stackoverflow.com/questions/27447865/understanding-the-simplest-llvm-ir
#include "built-in.h"
#include "sym-limits.h"

void gen_inc(int x, int r);
int inc(int x) {
	return x++;
}

void test_inc() {
	int x,r;
	x = mksym_i32();
	limit2_i32(&x, 2,28);
	r = inc(x);
	gen_inc(x,r);
}
