# ifndef __CVC4_ENGINE_HPP__
# define __CVC4_ENGINE_HPP__

// Project
# include "ismt-engine.hpp"
# include "expr.hpp"

namespace solver {
	class CVC4Engine final : public ISmtEngine {
		CVC4Engine();
		virtual ~CVC4Engine();
		virtual void AssertExpr (SharedExprPtr expr);
		virtual Sat CheckSat();
		virtual Value GetValue(SharedVariablePtr varible);
	};
}

# endif /* __CVC4_ENGINE_HPP__ */
