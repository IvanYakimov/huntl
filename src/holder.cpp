#include "holder.hpp"

namespace memory {
	bool IsSymbolic(HolderPtr holder) {
		return utils::instanceof<Symbolic>(holder);
	}

	bool IsConcrete(HolderPtr holder) {
		return not (utils::instanceof<Symbolic>(holder));
	}

	solver::SharedExpr GetExpr(memory::HolderPtr holder) {
		assert(memory::IsSymbolic(holder));
		solver::SharedExpr sym_expr = Object::UpCast<memory::Symbolic>(holder)->Get();
		return sym_expr;
	}

	interpreter::MetaInt GetValue(memory::HolderPtr holder) {
		assert(memory::IsConcrete(holder));
		interpreter::MetaInt concrete_val = Object::UpCast<memory::Concrete>(holder)->Get();
		return concrete_val;
	}
}













