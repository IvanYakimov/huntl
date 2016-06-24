#ifndef __SOLVER_HPP__
#define __SOLVER_HPP__

#include <cvc4/cvc4.h>

namespace solver {
	class Solver {
	public:
		Solver();
		~Solver();
		CVC4::ExprManager& ExprManager();
		CVC4::SmtEngine& SmtEngine();
		CVC4::SymbolTable& SymbolTable();
	private:
		CVC4::ExprManager expr_manager_;
		CVC4::SmtEngine smt_engine_;
		CVC4::SymbolTable symbol_table_;
	};
}

#endif














