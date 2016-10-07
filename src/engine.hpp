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
I32 binop_i32(Ref res, OpCode code, Flag flag, Ref arg1, I32 op1, Ref arg2, I32 op2);
I32 icmp_i32(Ref res, Cond cond, Ref op1, I32 v1, Ref op2, I32 v2);

}

#include <iostream>
int32_t Dummy();

#endif
