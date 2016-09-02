#include "../../lib/llvoyager/built-in.h"
#include "../../lib/string/string.c"

void init_dest(char *dest, size_t dest_len) {
	dest[0] = 'b';
	dest[1] = 'a';
	dest[2] = 's';
	dest[3] = 'e';
	dest[4] = ' ';
	dest[5] = '\0';
	dest[dest_len-1] = '\0';
}

#warning "strcat: strange behavior"
void gen_strcat(char *dest, const char *src, char *res);
void test_() {
	const size_t dest_len = 10, src_len = 5;
	char dest[dest_len], src[src_len], origin[dest_len];
	init_buff(src, src_len);
	//init_dest(dest, dest_len);
	init_buff(dest, dest_len);
	strcpy(origin, dest);
	char *res = strcat(dest, src);
	gen_strcat(origin, src, res);
}

void gen_strncat(char *dest, const char *src, size_t count, char *);
void test_strncat() {
	const size_t dest_len = 5, src_len = 2;
	char dest[dest_len], src[src_len], origin[dest_len];
	dest[src_len-1] = '\0';
	init_buff(dest, dest_len); init_buff(src, src_len);
	strcpy(origin, dest);
	char *res = strncat(dest, src, src_len-1);
	gen_strncat(origin, src, src_len-1, res);
}

size_t strlcat(char *dest, const char *src, size_t count);


