#include "solver.hpp"

namespace solver {
	Solver::Solver() : expr_manager_(), smt_engine_(&expr_manager_), symbol_table_() {

	}

	Solver::~Solver() {

	}

	CVC4::ExprManager& Solver::ExprManager() {
		return expr_manager_;
	}

	CVC4::SmtEngine& Solver::SmtEngine() {
		return smt_engine_;
	}

	CVC4::SymbolTable& Solver::SymbolTable() {
		return symbol_table_;
	}
}















