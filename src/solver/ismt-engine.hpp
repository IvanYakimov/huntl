#ifndef __ISMT_ENGINE_HPP__
#define __ISMT_ENGINE_HPP__

# include "expr.hpp"

namespace solver
{
	/** Enumeration of all available results from satisfiability checking.
	 * \see ISMTEngie::CheckSat
	 */
	typedef enum {
		/** There is no models for formulas in stack. */
		UNSAT,
		/** There is at least one model for formulars in stack. */
		SAT,
		/** Solver can't determine whether or not available any model for formulas in user formulas' stack. */
		UNKNOWN
	}Sat;

	/**
	 * Abstract interface for an abstract SMT-solver.
	 * \author Ivan Yakimov, e-mail: ivan.yakimov.research@yandex.ru
	 * \date 14.09.2015
	 */
	class ISMTEngine
	{
	public:
		virtual ~ISMTEngine() {}
		/** Asserts expression into the stack of user provided formulas. */
		virtual void Assert (ExprPtr expr) = 0;
		/** Checks satisifiabilty for formulas in the stack.
		 * \see Sat */
		virtual Sat CheckSat() = 0;
		/** Returns value of a variable if it's available.
		 * Throws logic_error if the variable doesn't bound.
		 * \see Value */
		virtual ValuePtr GetValue(ExprPtr varible) throw(std::logic_error) = 0;
		virtual void Push() = 0;
		virtual void Pop() = 0;
	private:
#ifdef DBG
	public:
#endif
		template <class T>
		T Prism(ExprPtr expr) throw(std::logic_error);
	};
}

#endif
