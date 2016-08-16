#include "built-in.h"
#include "sym-limits.h"
//#include <limits.h>

typedef unsigned long size_t;

void gen_strlen(const char *s, size_t res);
size_t strlen(const char *s)
{
	const char *sc;

	for (sc = s; *sc != '\0'; ++sc)
		;
	return sc - s;
}

void test_strlen() {
	unsigned char buff[5];
	for (int i = 0; i < 5; i++) {
		//buff[i] = 'a' + i;
		buff[i] = mksym_u8();//'a' + i;
		limit2_u8(&buff[i], '\0', 'Z');
	}
	buff[4] = '\0';
	size_t len;
	len = strlen(buff);
	gen_strlen(buff,len);
}

//TODO: debugging
/*
void gen_strcmp(const char *cs, const char *ct, int res);
int strcmp(const char *cs, const char *ct)
{
	unsigned char c1, c2;

	while (1) {
		c1 = *cs++;
		c2 = *ct++;
		if (c1 != c2)
			return c1 < c2 ? -1 : 1;
		if (!c1)
			break;
	}
	return 0;
}

void test_strcmp() {
	char b1[5];
	char b2[5];
	for (int i = 0; i < 5; i++) {
		b1[i] = i;
		b2[i] = i+1;
	}
	b1[4] = '\0'; b2[4] = '\0';
	int len = strcmp(b1,b2);
	gen_strcmp(b1,b2,len);
}
*/











