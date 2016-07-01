#include "solver.hpp"

namespace solver {
	Solver::Solver() : expr_manager_(), smt_engine_(&expr_manager_), symbol_table_() {
		path_constraint_ = utils::Create<PathConstraint>();
		smt_engine_.setOption("incremental", CVC4::SExpr("true"));
		smt_engine_.setOption("produce-models", CVC4::SExpr("true"));
		smt_engine_.setOption("rewrite-divk", CVC4::SExpr("true"));
		smt_engine_.setLogic("QF_BV");
	}

	Solver::~Solver() {

	}

	SolverPtr Solver::Create() {
		return utils::Create<Solver>();
	}

	CVC4::Expr GetExpr(memory::HolderPtr& holder) {
		assert(memory::IsSymbolic(holder)
						and "only a symbolic expression is allowed to be joined to the path-constraint");
		CVC4::Expr sym_expr = Object::UpCast<memory::Symbolic>(holder)->Get();
		return sym_expr;
	}

	void Solver::Constraint(memory::HolderPtr holder) {
		CVC4::Expr sym_expr = GetExpr(holder);
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

	bool Solver::CheckSat() {
		assert (false and "not implemented");
	}

	void Solver::ProduceModel() {
		assert (false and "not implemented");
	}

	interpreter::BitVec Solver::GetValue(memory::HolderPtr holder) {
		CVC4::Expr sym_expr = GetExpr(holder);
		CVC4::Expr res = smt_engine_.getValue(sym_expr);
		CVC4::BitVector val = res.getConst<CVC4::BitVector>();
		assert (false and "not implemented");
	}
}















