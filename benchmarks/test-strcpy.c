#include "built-in.h"
#include "string.c"

void gen_strcpy(char *dest, const char *src, char *res);

void test_1() {
	char buff1[6];
	char buff2[6];
	init_buff(buff1, 6);
	init_buff(buff2, 6);

	char *res = strcpy(buff1, buff2);
	gen_strcpy(buff1, buff2, res);
}
