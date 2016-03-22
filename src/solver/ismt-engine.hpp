#ifndef __ISMT_ENGINE_HPP__
#define __ISMT_ENGINE_HPP__

# include "expr.hpp"
#include "exception.hpp"

namespace solver
{
	class ScopeException : public Exception {
	public:
		virtual ~ScopeException() {}
		ScopeException() : Exception("cannot pop on zero scope level") {}
	};

	class ModelException : public Exception {
	public:
		virtual ~ModelException() {}
		ModelException() : Exception("model is not available") {}
	};

	class BindingException : public Exception {
	public:
		virtual ~BindingException() {}
		BindingException() : Exception("unbound variable") {}
	};

	/** Enumeration of all available results from satisfiability checking.
	 * \see ISMTEngie::CheckSat
	 */
	typedef enum {
		/** There is no model for the asserted formulas . */
		UNSAT,
		/** There is at least one model for the asserted formulars. */
		SAT,
		/** Solver can't determine whether or not available any model for the asserted formulas. */
		UNKNOWN
	}Sat;

	/**
	 * Abstract interface for a fragment of SMT-LIB compatible solver (only QF_BV logic is supported).
	 * Specification of this interface relies on SMT-LIB2 Standard Version 2.0.
	 * \author Ivan Yakimov, e-mail: ivan.yakimov.research@yandex.ru
	 * \date 14.09.2015
	 */
	class ISMTEngine
	{
	public:
		/** */
		virtual ~ISMTEngine() throw() {}
		/** Asserts expression into the assertions stack.
		 * During the SMT-LIB2 standard expr must be well sorted closed term of sort Bool.
		 * \throws ScopeError - one tries to assert expression at 0 scope level.
		 * \throws TypeCheckingError - one tries to asset malformed expression
		 * */
		virtual void Assert (ExprPtr expr) throw (TypeCheckingException, UnknownException)= 0;
		//TODO: exceptions handling
		/** Checks satisifiabilty of all the currently asserted formulas.
		 * \see Sat */
		virtual Sat CheckSat() = 0;
		/** Returns value of an expression if it is available.
		 * \throws BindingException - expr is an unbound variable
		 * \throws TypeCheckingException - type of passed variable isn't compatible with type of actual bound variable
		 * \throws ModelException - solver cannot returnvalue of expression without sat checking
		 * \throws ImplementationException - piece of code isn't implemented
		 * \throws UnknownException - wrapped solver throws an exception which isn't supported buy the abstract interface
		 * \see Value */
		virtual ValuePtr GetValue(ExprPtr varible)
			throw (BindingException, TypeCheckingException, ModelException, ImplementationException, UnknownException) = 0;
		/** Push new scope into the assertions stack */
		virtual void Push()
			throw () = 0;
		/** Pop scope from the assertions stack.
		 * \throws ScopeException - one tries to pop scope on zero level */
		virtual void Pop()
			throw (ScopeException) = 0;
	private:
#ifdef DBG
	public:
#endif
		//TODO: exceptions handling
		template <class T>
		T Prism(ExprPtr expr) throw(std::logic_error);
	};
}

#endif
