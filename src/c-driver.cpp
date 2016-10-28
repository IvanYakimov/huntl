#include "c-driver.hpp"

extern "C" {
	//***********************************************************************
	//** Warning: this file was generated automatically, don't edit it by hands **
	//***********************************************************************
	//alloca
	void alloca_I8(Ref res, I8 allocator){
		cpp_alloca_I8(res, allocator);
	}

	void alloca_I16(Ref res, I16 allocator){
		cpp_alloca_I16(res, allocator);
	}

	void alloca_I32(Ref res, I32 allocator){
		cpp_alloca_I32(res, allocator);
	}

	void alloca_I64(Ref res, I64 allocator){
		cpp_alloca_I64(res, allocator);
	}

	//binop
	void binop_I8(Ref res, OpCode code, Flag flag, Ref arg1, I8 op1, Ref arg2, I8 op2){
		cpp_binop_I8(res, code, flag, arg1, op1, arg2, op2);
	}

	void binop_I16(Ref res, OpCode code, Flag flag, Ref arg1, I16 op1, Ref arg2, I16 op2){
		cpp_binop_I16(res, code, flag, arg1, op1, arg2, op2);
	}

	void binop_I32(Ref res, OpCode code, Flag flag, Ref arg1, I32 op1, Ref arg2, I32 op2){
		cpp_binop_I32(res, code, flag, arg1, op1, arg2, op2);
	}

	void binop_I64(Ref res, OpCode code, Flag flag, Ref arg1, I64 op1, Ref arg2, I64 op2){
		cpp_binop_I64(res, code, flag, arg1, op1, arg2, op2);
	}

	//icmp
	void icmp_I8(Ref res, I8 op1, I8 op2){
		cpp_icmp_I8(res, op1, op2);
	}

	void icmp_I16(Ref res, I16 op1, I16 op2){
		cpp_icmp_I16(res, op1, op2);
	}

	void icmp_I32(Ref res, I32 op1, I32 op2){
		cpp_icmp_I32(res, op1, op2);
	}

	void icmp_I64(Ref res, I64 op1, I64 op2){
		cpp_icmp_I64(res, op1, op2);
	}

	//ite
	bool ite(Ref ret, bool cond){
		return cpp_ite(ret, cond);
	}


}