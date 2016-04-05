# ifndef __CVC4_ENGINE_HPP__
# define __CVC4_ENGINE_HPP__

// cvc4
# include <cvc4/cvc4.h>

// STL
# include <exception>

// Project
# include "ismt-engine.hpp"
# include "expr.hpp"
# include "expr-manager.hpp"
# include "value.hpp"

// STL
# include <memory>

namespace solver {
	/** A wrapper for CVC4 engine in context of ISMTSolver infrastructure. */
	class CVC4Engine final : public ISMTEngine {
	public:
		/** Basic constructor. Provides all necessary initialization for creation of instance for the cvc4 solver's wrapper,
		 * you can use it directlry.
		 */
		CVC4Engine();
		virtual ~CVC4Engine() throw() final;
		/** \see ISMTEngine::Assert */
		virtual void Assert(ExprPtr expr) throw(TypeCheckingException, UnknownException) final;
		/** \see ISMTEngine::CheckSat */
		virtual Sat CheckSat() final;
		/** \see ISMTEngine::GetValue */
		virtual ValuePtr GetValue(ExprPtr varible)
			throw (BindingException, TypeCheckingException, ModelException, ImplementationException, UnknownException)final;
		/** \see ISMTEngine::Push */
		virtual void Push() throw() final;
		/** \see ISMTEngiine::Pop */
		virtual void Pop() throw (ScopeException) final;
	private:
#ifdef DBG
	public:
#endif
		/** \see ISMTEngine::Prism */
		CVC4::Expr Prism(ExprPtr expr)
			throw(IllegalArgException, CastingException, ImplementationException);
		/** Expression manager, provides creation and memory management for CVC4 expressions.
		 * See CVC4 documentation for details. */
		CVC4::ExprManager expr_manager_;
		/** SMT engine provides commands, available for smt-lib2 standard. */
		CVC4::SmtEngine smt_engine_;
		/** Symbol table - provides scopes and variables management. */
		CVC4::SymbolTable symbol_table_;
	};
}

# endif /* __CVC4_ENGINE_HPP__ */
