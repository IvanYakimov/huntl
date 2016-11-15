#ifndef __LLVOYAGER_BUILT_IN__
#define __LLVOYAGER_BUILT_IN__

char mksym_i8() {return 0;}
short mksym_i16() {return 0;}
int mksym_i32() {return 0;}
long mksym_i64() {return 0;}

unsigned char	mksym_u8()	{return 0;}
unsigned short	mksym_u16()	{return 0;}
unsigned int	mksym_u32()	{return 0;}
unsigned long	mksym_u64() {return 0;}

#endif

#ifndef __INIT_BUFF__
#define __INIT_BUFF__

void init_buff(char* buff, int len) {
  for (int i = 0; i < len; i++) {
    buff[i] = mksym_i8();
  }
  buff[len-1] = '\0';
}

void init_int_buff(int buff[], int len) {
  for (int i = 0; i < len; i++) {
    buff[i] = mksym_i32();
  }
}

void cpy_int_buff(int dest[], const int src[], int len) {
  for (int i = 0; i < len; i++) {
    dest[i] = src[i];
  }
}


#endif

#ifndef __SYM_LIMITS__
#define __SYM_LIMITS__

void limit2_i8(char* x, char lower, char upper) {
  if (*x >= upper)
    *x = upper;
  else if (*x <= lower)
    *x = lower;
}

void limit2_i16(short* x, short lower, short upper) {
  if (*x >= upper)
    *x = upper;
  else if (*x <= lower)
    *x = lower;
}

void limit2_i32(int* x, int lower, int upper) {
  if (*x >= upper)
    *x = upper;
  else if (*x <= lower)
    *x = lower;
}

void limit2_i64(long* x, long lower, long upper) {
  if (*x >= upper)
    *x = upper;
  else if (*x <= lower)
    *x =  lower;
}

void limit2_u8(unsigned char* x, unsigned char lower, unsigned char upper) {
  if (*x >= upper)
    *x = upper;
  else if (*x <= lower)
    *x =  lower;
}

void limit2_u16(unsigned short* x, unsigned short lower, unsigned short upper) {
  if (*x >= upper)
    *x = upper;
  else if (*x <= lower)
    *x =  lower;
}


void limit2_u32(unsigned int* x, unsigned int lower, unsigned int upper) {
  if (*x >= upper)
    *x = upper;
  else if (*x <= lower)
    *x =  lower;
}

void limit2_u64(unsigned long* x, unsigned long lower, unsigned long upper) {
  if (*x >= upper)
    *x = upper;
  else if (*x <= lower)
    *x =  lower;
}

#endif
