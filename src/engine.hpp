#ifndef __ENGINE_HPP__
#define __ENGINE_HPP__

extern "C" {
#include <stdint.h>
#include "opcodes.h"
typedef I32 int32_t;
typedef uint64_t Ref;
int32_t add(Ref x);
// replace with macro (if possible without "tricky" code")
int32_t binop_i32(OpCode code, Ref x, int8_t flag, Ref y, I32 op1, Ref z, int32_t op2, int8_t* status);
}

#include <iostream>
int32_t Dummy(Ref x);

#endif
