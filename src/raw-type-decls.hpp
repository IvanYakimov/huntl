#ifndef __RAW_TYPE_DECLS_HPP__
#define __RAW_TYPE_DECLS_HPP__

extern "C" {
#include <stdint.h>
typedef unsigned int OpCode;
typedef unsigned int Cond;
typedef int8_t I8;
typedef int16_t I16;
typedef int32_t I32;
typedef int64_t I64;
typedef uint64_t Ref;
typedef uint16_t Flag;
}

#endif
