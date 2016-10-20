#ifndef __ENGINE_HPP__
#define __ENGINE_HPP__

extern "C" {
#include <stdint.h>
typedef unsigned int OpCode;
typedef unsigned int Cond;
typedef int32_t I32;
typedef uint64_t Ref;
typedef uint16_t Flag;
int32_t add(Ref x);
//TODO: replace with a macro
//TODO: rename args
void binop_i32(Ref res, OpCode code, Flag flag, Ref arg1, I32 op1, Ref arg2, I32 op2);
void icmp_i32(Ref res, Cond cond, Ref op1, I32 v1, Ref op2, I32 v2);
void alloca_i32(Ref res, I32 allocator);
void load(Ref res, Ref target);
void store_i32(I32 value, Ref ptr);
void store_ref(Ref value, Ref ptr);
bool ite(Ref ref, bool cond);
}

#include <iostream>
int32_t Dummy();

#endif
