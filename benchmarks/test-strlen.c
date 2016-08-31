#include "built-in.h"
#include "string.c"

void gen_strlen(const char *s, size_t res);


void test_strlen() {
	char buff[6];
	for (int i = 0; i < 6; i++) {
		buff[i] = mksym_i8();//'a' + i;
	}
	size_t len;
	len = strlen(buff);
	gen_strlen(buff,len);
}
