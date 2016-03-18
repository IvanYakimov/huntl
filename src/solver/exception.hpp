#ifndef __SOLVER_EXCEPTION_HPP__
#define __SOLVER_EXCEPTION_HPP__

#include <stdexcept>

namespace solver {
	class Exception : std::logic_error {
	public:
		Exception(const char* msg) : logic_error(msg) {}
		virtual ~Exception() {}
	};
}

#endif
