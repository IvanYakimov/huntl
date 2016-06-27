#include "holder.hpp"

namespace memory {
	bool IsSymbolic(HolderPtr holder) {
		return utils::instanceof<Symbolic>(holder);
	}

	bool IsConcrete(HolderPtr holder) {
		return not (utils::instanceof<Symbolic>(holder));
	}
}













