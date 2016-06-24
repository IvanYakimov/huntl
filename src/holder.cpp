#include "holder.hpp"

namespace memory {
	Undef::Undef() {}
	HolderPtr Undef::Create(){
		return std::make_shared<Undef>();
	}

	bool IsSymbolic(HolderPtr holder) {
		return utils::instanceof<Symbolic>(holder);
	}

	bool IsUndef(HolderPtr holder) {
		return utils::instanceof<Undef>(holder);
	}

	bool IsConcrete(HolderPtr holder) {
		return not (utils::instanceof<Symbolic>(holder)
				or utils::instanceof<Undef>(holder));
	}
}













