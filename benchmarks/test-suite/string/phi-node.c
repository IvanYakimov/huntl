#include "../../lib/llvoyager/built-in.h"

void test_() {
	int x = 0, y = 0, z = 0;
	y = mksym_i32();
	z = mksym_i32();
	x = y || z;
}
