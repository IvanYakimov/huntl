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

	class ImplementationException : public Exception {
	public:
		virtual ~ImplementationException () {}
		ImplementationException() : Exception("not implemented") {}
	};

	class IllegalArgException : public Exception {
	public:
		virtual ~IllegalArgException () {}
		IllegalArgException() : Exception("illegal argument(s)") {}
	};

	class TypeCheckingException : public Exception {
	public:
		virtual ~TypeCheckingException () {}
		TypeCheckingException() : Exception("type checking error") {}
	};

	class CastingException : public Exception {
	public:
		virtual ~CastingException() {}
		CastingException() : Exception("casting failure") {}
	};
}

#endif












