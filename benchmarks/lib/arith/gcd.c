//#include <linux/kernel.h>
//#include <linux/gcd.h>
//#include <linux/export.h>

/*
 * This implements the binary GCD algorithm. (Often attributed to Stein,
 * but as Knuth has noted, appears in a first-century Chinese math text.)
 *
 * This is faster than the division-based algorithm even on x86, which
 * has decent hardware division.
 */


// <-- from <linux/kernel.h>: 
/*
 * swap - swap value of @a and @b
 */
#define swap(a, b) \
	do { typeof(a) __tmp = (a); (a) = (b); (b) = __tmp; } while (0)
// -->

/* If normalization is done by loops, the even/odd algorithm is a win. */
unsigned long gcd(unsigned long a, unsigned long b)
{
	unsigned long r = a | b;

	if (!a || !b)
		return r;

	/* Isolate lsbit of r */
	r &= -r;

	while (!(b & r))
		b >>= 1;
	if (b == r)
		return r;

	for (;;) {
		while (!(a & r))
			a >>= 1;
		if (a == r)
			return r;
		if (a == b)
			return a;

		if (a < b)
			swap(a, b);
		a -= b;
		a >>= 1;
		if (a & r)
			a += b;
		a >>= 1;
	}
}
