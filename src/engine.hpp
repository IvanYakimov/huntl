#ifndef __ENGINE_HPP__
#define __ENGINE_HPP__

extern "C" {
#include <stdint.h>
typedef unsigned int OpCode;
typedef unsigned int Cond;
// also replace by macro
typedef int8_t i8;
typedef int16_t i16;
typedef int32_t i32;
typedef int64_t i64;
typedef int32_t I32;
typedef uint64_t Ref;
typedef uint16_t Flag;
int32_t add(Ref x);
//TODO: replace with a macro
//TODO: rename args
//-------------------------------------------------------
// Somehow a "grammar" for interpreter-call handlers
#define BINOP binop_
#define BINOP_ARGS(T)	(Ref res, OpCode code, Flag flag, Ref arg1, T op1, Ref arg2, T op2)
#define ICMP_PRE() icmp_
#define ICMP_ARGS(T)	(Ref res, T allocator)
#define ALLOCA alloca_

#define FUNC_HEAD(T, name, header)	void name ## T header(T)

// BinOp:
FUNC_HEAD(i8, BINOP, BINOP_ARGS);
FUNC_HEAD(i16, BINOP, BINOP_ARGS);
FUNC_HEAD(i32, BINOP, BINOP_ARGS);
FUNC_HEAD(i64, BINOP, BINOP_ARGS);
// ICmp:
FUNC_HEAD(i8, icmp_, ICMP_ARGS);
FUNC_HEAD(i16, icmp_, ICMP_ARGS);
FUNC_HEAD(i32, icmp_, ICMP_ARGS);
FUNC_HEAD(i64, icmp_, ICMP_ARGS);
//
//void binop_i32(Ref res, OpCode code, Flag flag, Ref arg1, I32 op1, Ref arg2, I32 op2);
//void icmp_i32(Ref res, Cond cond, Ref op1, I32 v1, Ref op2, I32 v2);
void alloca_i32(Ref res, I32 allocator);
void load(Ref res, Ref target);
void store_i32(I32 value, Ref ptr);
void store_ref(Ref value, Ref ptr);
bool ite(Ref ref, bool cond);
void ret_i32(Ref res, Ref op, I32 val);
}

#include <iostream>
int32_t Dummy();

#endif
