#ifndef __CONTEXT_HPP__
#define __CONTEXT_HPP__

#include <cvc4/cvc4.h>

namespace solver {
	class Context;
	using ContextRef = Context&;
	class Context {
	public:
		Context();
		virtual ~Context();
		CVC4::ExprManager& ExprManger();
		CVC4::SmtEngine& SmtEngine();
		CVC4::SymbolTable& SymbolTable();
	private:
		CVC4::ExprManager expr_manager_;
		CVC4::SmtEngine smt_engine_;
		CVC4::SymbolTable symbol_table_;
	};
}

#endif
