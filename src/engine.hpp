#ifndef __ENGINE_HPP__
#define __ENGINE_HPP__

extern "C" {
#include <stdint.h>
  typedef unsigned int OpCode;
typedef int32_t I32;
typedef uint64_t Ref;
typedef uint16_t Flag;
int32_t add(Ref x);
// TODO: replace with a macro 
I32 binop_i32(Ref a, OpCode code, Flag flag, Ref b, I32 op1, Ref c, int32_t op2);
}

#include <iostream>
int32_t Dummy();

#endif
