#include "solver.hpp"

namespace solver {
	Solver::Solver() : expr_manager_(), smt_engine_(&expr_manager_), symbol_table_() {
		path_constraint_ = utils::Create<PathConstraint>();
	}

	Solver::~Solver() {

	}

	SolverPtr Solver::Create() {
		return utils::Create<Solver>();
	}

	void Solver::Constraint(memory::HolderPtr holder) {
		assert (memory::IsSymbolic(holder) and "only a symbolic expression is allowed to be joined to the path-constraint");
		SharedExpr sym_expr = Object::UpCast<memory::Symbolic>(holder)->Get();
		SmtEngine().assertFormula(sym_expr);
		path_constraint_->push_back(holder);
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















