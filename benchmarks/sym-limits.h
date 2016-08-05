#ifndef __SYM_LIMITS_H__
#define __SYM_LIMITS_H__

short limit_i16(short x, short lower, short upper) {
	if (x >= upper)
		return upper;
	else if (x <= lower)
		return lower;
	else
		return x;
}

void limit2_i16(short *x, short lower, short upper) {
	if (*x >= upper)
		*x = upper;
	else if (*x <= lower)
		*x = lower;
	else
		*x = *x;
}

int limit_i32(int x, int lower, int upper) {
	if (x >= upper)
		return upper;
	else if (x <= lower)
		return lower;
	else
		return x;
}

long limit_i64(long x, long lower, long upper) {
	if (x >= upper)
		return upper;
	else if (x <= lower)
		return lower;
	else
		return x;
}

void limit2_i32(int* x, int lower, int upper) {
	if (*x >= upper)
		*x = upper;
	else if (*x <= lower)
		*x = lower;
	else
		*x = *x;
}

void limit2_i64(long* x, long lower, long upper) {
	if (*x >= upper)
		*x = upper;
	else if (*x <= lower)
		*x =  lower;
	else
		*x = *x;
}

void limit2_u8(unsigned char* x, unsigned char lower, unsigned char upper) {
	if (*x >= upper)
		*x = upper;
	else if (*x <= lower)
		*x =  lower;
	else
		*x = *x;
}

void limit2_u16(unsigned short* x, unsigned short lower, unsigned short upper) {
	if (*x >= upper)
		*x = upper;
	else if (*x <= lower)
		*x =  lower;
	else
		*x = *x;
}


void limit2_u32(unsigned int* x, unsigned int lower, unsigned int upper) {
	if (*x >= upper)
		*x = upper;
	else if (*x <= lower)
		*x =  lower;
	else
		*x = *x;
}

void limit2_u64(unsigned long* x, unsigned long lower, unsigned long upper) {
	if (*x >= upper)
		*x = upper;
	else if (*x <= lower)
		*x =  lower;
	else
		*x = *x;
}

unsigned int limit_u32(unsigned int x, unsigned int lower, unsigned int upper) {
	if (x >= upper)
		return upper;
	else if (x <= lower)
		return lower;
	else
		return x;
}

unsigned long limit_u64(unsigned long x, unsigned long lower, unsigned long upper) {
	if (x >= upper)
		return upper;
	else if (x <= lower)
		return lower;
	else
		return x;
}

#endif
