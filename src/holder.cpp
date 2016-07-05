#include "holder.hpp"

namespace memory {
	bool IsSymbolic(HolderPtr holder) {
		return utils::instanceof<Symbolic>(holder);
	}

	bool IsConcrete(HolderPtr holder) {
		return not (utils::instanceof<Symbolic>(holder));
	}

	const solver::SharedExpr& GetExpr(memory::HolderPtr holder) {
		assert(memory::IsSymbolic(holder));
		return Object::UpCast<memory::Symbolic>(holder)->Get();
	}

	const interpreter::MetaInt& GetValue(memory::HolderPtr holder) {
		assert(memory::IsConcrete(holder));
		return Object::UpCast<memory::Concrete>(holder)->Get();
	}
}













