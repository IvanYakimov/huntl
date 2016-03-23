#ifndef __SOLVER_EXCEPTION_HPP__
#define __SOLVER_EXCEPTION_HPP__

#include <stdexcept>

namespace solver {
	/** Basic type of the solver exception.
	 * Every user-defined exception in the solver namespace must be inherited from it  */
	class Exception : public std::logic_error {
	public:
		Exception(const char* msg) : logic_error(msg) {}
		virtual ~Exception() {}
	};

	/** Default (not a basic) exception. It should be used for unknown exceptions
	 * \param msg - some explanation of a problem */
	class UnknownException : public Exception {
	public:
		virtual ~UnknownException () {}
		UnknownException(const char* msg) : Exception(msg) {}
	};

	/** Throws if an unimplemented feature is invoked while the program exectution */
	class ImplementationException : public Exception {
	public:
		virtual ~ImplementationException () {}
		ImplementationException() : Exception("not implemented") {}
	};

	/** Throws if caller tries to invoke some method/function with one or more illegal argument(s) */
	class IllegalArgException : public Exception {
	public:
		virtual ~IllegalArgException () {}
		IllegalArgException() : Exception("illegal argument(s)") {}
	};

	/** Throws if a type checking error occurs */
	class TypeCheckingException : public Exception {
	public:
		virtual ~TypeCheckingException () {}
		TypeCheckingException() : Exception("type checking error") {}
	};

	/** Throws if (smart pointers to) objects casting is failed */
	class CastingException : public Exception {
	public:
		virtual ~CastingException() {}
		CastingException() : Exception("casting failure") {}
	};
}

#endif












