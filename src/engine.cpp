#include "engine.hpp"

extern "C" {
	// BinOp:
	FUNC_HEAD(i8, binop_, BINOP_ARGS) {

	}

	FUNC_HEAD(i16, binop_, BINOP_ARGS) {

	}

	FUNC_HEAD(i32, binop_, BINOP_ARGS) {

	}

	FUNC_HEAD(i64, binop_, BINOP_ARGS) {

	}

	// ICmp:
	FUNC_HEAD(i8, icmp_, ICMP_ARGS) {}
	FUNC_HEAD(i16, icmp_, ICMP_ARGS) {}
	FUNC_HEAD(i32, icmp_, ICMP_ARGS) {}
	FUNC_HEAD(i64, icmp_, ICMP_ARGS) {}

	void alloca_i32(Ref res, I32 allocator) {

	}

	void load(Ref res, Ref target) {

	}

	void store_i32(I32 value, Ref ptr) {

	}

	void store_ref(Ref value, Ref ptr) {

	}

	bool ite(Ref ref, bool cond) {

	}

	void ret_i32(Ref res, Ref op, I32 val) {

	}
}

int32_t Dummy() {
	std::cout << "handler catched\n";
}












