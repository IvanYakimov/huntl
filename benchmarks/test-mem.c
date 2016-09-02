#include "built-in.h"
#include "string.c"

#warning "memset: fails everytime"
void gen_memset(void *s, int c, size_t count, void *res);
void test_memset() {
	const size_t size = 6;
	char s[size], origin[size];
	char c = mksym_i32();
	init_buff(s, size);
	strcpy(origin, s);
	void *r = memset(s, c, size);
	gen_memset(origin,c,size, r);
}

void gen_memcpy(void *dest, const void *src, size_t count, void *res);
void test_memcpy() {
	const size_t count = 6;
	char dest[count], src[count], origin[count];
	init_buff(dest, count); init_buff(src, count);
	strcpy(origin, dest);
	void *r = memcpy(dest, src, count);
	gen_memcpy(origin, src, count, r);
}

void *memmove(void *dest, const void *src, size_t count);
int memcmp(const void *cs, const void *ct, size_t count);
void *memscan(void *addr, int c, size_t size);
