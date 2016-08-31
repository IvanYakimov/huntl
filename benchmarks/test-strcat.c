#include "built-in.h"
#include "string.c"

#error "LL-VOYAGER runtime error"

void gen_strcat(char *dest, const char *src, char *res);

void test_() {
	char buff1[11];
	char buff2[5];
	char *res = strcat(buff1, buff2);
	gen_strcat(buff1, buff2, res);
}
