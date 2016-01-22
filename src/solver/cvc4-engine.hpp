# ifndef __CVC4_ENGINE_HPP__
# define __CVC4_ENGINE_HPP__

// cvc4
# include <cvc4/cvc4.h>

// Project
# include "ismt-engine.hpp"
# include "expr.hpp"
# include "../../src/utils/memory.hpp"

// STL
# include <memory>

namespace solver {
	class CVC4Engine final : public ISMTEngine {
	public:
		CVC4Engine();
		virtual ~CVC4Engine();
		virtual void Assert(SharedExprPtr expr) final;
		virtual Sat CheckSat() final;
		virtual std::int32_t GetValue(SharedExprPtr varible) final;
		virtual void Push() final;
		virtual void Pop() final;
	private:
		CVC4::Expr Prism(SharedExprPtr expr);
		CVC4::ExprManager expr_manager_;
		std::unique_ptr<CVC4::SmtEngine> smt_engine_;
		CVC4::SymbolTable symbol_table_;
	};
}

# endif /* __CVC4_ENGINE_HPP__ */
