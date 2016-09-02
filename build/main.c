#include <stdio.h>

char *strpbrk(const char *cs, const char *ct)
{
	const char *sc1, *sc2;

	for (sc1 = cs; *sc1 != '\0'; ++sc1) {
		for (sc2 = ct; *sc2 != '\0'; ++sc2) {
			if (*sc1 == *sc2)
				return (char *)sc1;
		}
	}
	return NULL;
}

char *strreplace(char *s, char old, char new)
{
	for (; *s; ++s)
		if (*s == old)
			*s = new;
	return s;
}

/*
strpbrk: &"guinc" &"aeiou" => &"uinc"
strpbrk: &"vounm" &"aeiou" => &"ounm"
strpbrk: &"binba" &"aeiou" => &"inba"
strpbrk: &"wefaw" &"aeiou" => &"efaw"
strpbrk: &"fastm" &"aeiou" => &"astm"
strpbrk: &"umtup" &"aeiou" => &"umtup"
strpbrk: &"oasdc" &"aeiou" => &"oasdc"
strpbrk: &"ipmgt" &"aeiou" => &"ipmgt"
strpbrk: &"etbrh" &"aeiou" => &"etbrh"
strpbrk: &"ayurp" &"aeiou" => &"ayurp"
 */

int main() {
  char str[] = "string";
  char old = 's';
  char new = 'a';
  char *res = strreplace(str, old, new);
  printf("'\%s\'\n", res);
}
