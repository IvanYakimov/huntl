#include "built-in.h"
#include "string.c"

#warning "strcpy: all OK"
void gen_strcpy(char *dest, const char *src, char *res);
void test_strcpy() {
	const size_t len = 6;
	char dest[len], src[len], origin[len];
	init_buff(dest, len); init_buff(src, len);
	strcpy(origin, dest);
	char *res = strcpy(dest, src);
	gen_strcpy(origin, src, res);
}

#warning "strncpy: all OK."
void gen_strncpy(char *dest, const char *src, size_t count, char *res);
void test_strncpy() {
	const size_t len = 6;
	char dest[len], src[len], origin[len];
	init_buff(dest,len); init_buff(src,len);
	strcpy(origin, dest);
	char *res = strncpy(dest,src,len-1);
	gen_strncpy(origin,src,len-1,res);
}

#warning "strlcpy: fails everytime phi-node and llvm.memcpy.p0i8.p0i8.pi08.pi64	are required"
void gen_strlcpy(char *dest, const char *src, size_t size, size_t res);
void test_strlcpy() {
	const size_t len = 6;
	char s1[len], s2[len], origin[len];
	init_buff(s1,len); init_buff(s2,len);
	strcpy(origin,s1);
	size_t res = strlcpy(s1,s2,len-1);
	gen_strlcpy(s1,s2,len-1,res);
}
