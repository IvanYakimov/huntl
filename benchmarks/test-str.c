//#include "built-in.h"
//#include "sym-limits.h"
#include "str.c"

void gen_strlen(const char *cs, int res);

void test() {
	char target[] = "hello";
	size_t res = strlen(target);
	gen_strlen(target,res);
}


