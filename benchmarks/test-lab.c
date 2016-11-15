// see http://stackoverflow.com/questions/27447865/understanding-the-simplest-llvm-ir
#include "built-in.h"

void gen_inc(char x, char r);
char inc(char x) {
	return x;
}

void test_inc() {
	char x,r;
	x = mksym_i8();
	limit2_i8(&x, 0,127);
	r = inc(x);
	gen_inc(x,r);
}
