//#include "built-in.h"
//#include "sym-limits.h"
#include "str.c"

void gen_strlen(const char *cs, size_t res);
void mksym_str(char* str, int n);
void str_hello(char* str, int n);

void test_() {
	char target[6];
	str_hello(target, 6);
	size_t res = strlen(target);
	gen_strlen(target,res);
}


