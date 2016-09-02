#include "../../lib/llvoyager/built-in.h"
#include "../../lib/string/string.c"

#warning "don't work"

void gen_strchr(const char *s, int c, char *res);
void gen_strchrnul(const char *s, int c, char *res);
void gen_strrchr(const char *s, int c, char *res);
void gen_strnchr(const char *s, size_t count, int c, char *res);

void test_strchr() {
	const int len = 5;
	char s[len];
	init_buff(s, len);
	int c = mksym_i32();
	char *res = strchr(s, c);
	gen_strchr(s, c, res);
}

void test_strchrnul() {
	const int len = 5;
	char s[len];
	init_buff(s, len);
	int c = mksym_i32();
	char *res = strchrnul(s, c);
	gen_strchrnul(s, c, res);
}

void test_strrchr() {
	const int len = 5;
	char s[len];
	init_buff(s, len);
	int c = mksym_i32();
	char *res = strrchr(s, c);
	gen_strrchr(s, c, res);
}

void test_strnchr() {
	const int len = 5;
	char s[len];
	init_buff(s, len);
	int c = mksym_i32();
	int n = 4;
	char *res = strnchr(s, n, c);
	gen_strnchr(s, n, c, res);
}
