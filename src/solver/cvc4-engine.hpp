# ifndef __CVC4_ENGINE_HPP__
# define __CVC4_ENGINE_HPP__

// cvc4
# include <cvc4/cvc4.h>

// STL
# include <exception>

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
		virtual void Assert(SharedExpr expr) final;
		virtual Sat CheckSat() final;
		virtual std::int32_t GetValue(SharedExpr varible) final;
		virtual void Push() final;
		virtual void Pop() final;
#ifndef DBG
	private:
#endif
		CVC4::Expr Prism(SharedExpr expr);
		std::int32_t FromBitVector(CVC4::BitVector btv_const);
		CVC4::ExprManager expr_manager_;
		CVC4::SmtEngine smt_engine_;
		CVC4::SymbolTable symbol_table_;
		//TODO: add usage in the source file
		CVC4::Type btv32_;
	};
}

# endif /* __CVC4_ENGINE_HPP__ */
