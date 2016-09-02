#include "../../lib/llvoyager/built-in.h"
#include "../../lib/string/string.c"

void gen_strlen(const char *s, size_t res);
void test_strlen() {
	const size_t count = 6;
	char s[count];
	init_buff(s, count);
	size_t len = strlen(s);
	gen_strlen(s, len);
}

void gen_strnlen(const char *s, size_t count, size_t res);
void test_strnlen() {
	const size_t count = 6;
	char s[count];
	init_buff(s, count);
	size_t len = strnlen(s, count);
	gen_strnlen(s, count, len);
}
