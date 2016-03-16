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
# include "../../src/utils/memory.hpp"

// STL
# include <memory>

namespace solver {
	class CVC4Engine final : public ISMTEngine {
	public:
		CVC4Engine();
		virtual ~CVC4Engine();
		virtual void Assert(ExprPtr expr) final;
		virtual Sat CheckSat() final;
		virtual ValuePtr GetValue(ExprPtr varible) throw(std::logic_error) final;
		virtual void Push() final;
		virtual void Pop() final;
	private:
#ifdef DBG
	public:
#endif
		CVC4::Expr Prism(ExprPtr expr) throw(std::logic_error);
		CVC4::ExprManager expr_manager_;
		CVC4::SmtEngine smt_engine_;
		CVC4::SymbolTable symbol_table_;
	};
}

# endif /* __CVC4_ENGINE_HPP__ */
