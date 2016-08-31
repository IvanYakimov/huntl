#include "built-in.h"
#include "string.c"

void gen_strlen(const char *s, size_t res);


void test_strlen() {
	char buff[6];
	init_buff(buff,6);
	size_t len = strlen(buff);
	gen_strlen(buff,len);
}
