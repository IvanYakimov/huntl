#include "holder.hpp"

namespace memory {
	Undef::Undef() {}
	HolderPtr Undef::Create(){
		return utils::Create<Holder, Undef>();
	}
	bool Undef::Equals (const Object& rhs) const {
		auto cmp = [] (const Undef& l, const Undef& r) -> bool {
			return true;
		};
		return EqualsHelper<Undef>(*this, rhs, cmp);
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













