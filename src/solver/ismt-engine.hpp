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
		/** There is no models for formulas in stack. */
		UNSAT,
		/** There is at least one model for formulars in stack. */
		SAT,
		/** Solver can't determine whether or not available any model for formulas in stack. */
		UNKNOWN
	}Sat;

	/**
	 * Abstract interface for an abstract SMT-solver.
	 * Specification of this interface relies on SMT-LIB2 Standard Version 2.0.
	 * \author Ivan Yakimov, e-mail: ivan.yakimov.research@yandex.ru
	 * \date 14.09.2015
	 */
	class ISMTEngine
	{
	public:
		/** */
		virtual ~ISMTEngine() {}
		/** Asserts expression into the stack of user provided formulas.
		 * \throws logic_error - one tries to assert expression at 0 scope level. */
		virtual void Assert (ExprPtr expr) throw (std::logic_error)= 0;
		/** Checks satisifiabilty for formulas in the stack.
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
		/** Push new scope into stack */
		virtual void Push()
			throw () = 0;
		/** Pop scope from stack.
		 * \throws ScopeException - one tries to pop scope on zero level */
		virtual void Pop()
			throw (ScopeException) = 0;
	private:
#ifdef DBG
	public:
#endif
		template <class T>
		T Prism(ExprPtr expr) throw(std::logic_error);
	};
}

#endif
