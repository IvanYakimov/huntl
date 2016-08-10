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
	char buff[5];
	for (int i = 0; i < 5; i++) {
		buff[i] = 'a' + i;
	}
	size_t len;
	len = strlen(buff);
	gen_strlen(buff,len);
}












