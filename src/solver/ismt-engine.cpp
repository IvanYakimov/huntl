#include "ismt-engine.hpp"

namespace solver {
	const char * ScopeException::what() const noexcept {
		return "can't pop on zero scope level";
	}
}
