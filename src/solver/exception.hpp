#ifndef __SOLVER_EXCEPTION_HPP__
#define __SOLVER_EXCEPTION_HPP__

#include <stdexcept>

namespace solver {
	class Exception : public std::logic_error {
	public:
		Exception(const char* msg) : logic_error(msg) {}
		virtual ~Exception() {}
	};

	class UnknownException : public Exception {
	public:
		virtual ~UnknownException () {}
		UnknownException(const char* msg) : Exception(msg) {}
	};

	class ImplementException : public Exception {
	public:
		virtual ~ImplementException () {}
		ImplementException() : Exception("not implemented") {}
	};
}

#endif
