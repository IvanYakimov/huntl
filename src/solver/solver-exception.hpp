#ifndef __SOLVER_EXCEPTION_HPP__
#define __SOLVER_EXCEPTION_HPP__

#include <exception>

namespace solver {
	class SolverException {
	public:
		virtual ~SolverException() {}
		virtual const char * what() const = 0;
	};
}

#endif
