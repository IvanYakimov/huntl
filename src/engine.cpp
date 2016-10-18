#include "engine.hpp"

extern "C" {
	void binop_i32(Ref a, OpCode code, Flag flag, Ref b, I32 op1, Ref c, int32_t op2) {
		Dummy();
	}

	void icmp_i32(Ref res, Cond cond, Ref op1, I32 v1, Ref op2, I32 v2) {
		Dummy();
	}

	void alloca_i32(Ref res, I32 allocator) {

	}

	void load(Ref res, Ref target) {

	}
}

int32_t Dummy() {
	std::cout << "handler catched\n";
}
