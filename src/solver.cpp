#include "solver.hpp"

namespace solver {
	using utils::MetaKind;

	Solver::Solver() : expr_manager_(), smt_engine_(&expr_manager_), symbol_table_(), path_constraint_() {
		smt_engine_.setOption("incremental", CVC4::SExpr("true"));
		smt_engine_.setOption("produce-models", CVC4::SExpr("true"));
		smt_engine_.setOption("rewrite-divk", CVC4::SExpr("true"));
		smt_engine_.setLogic("QF_BV");
	}

	Solver::~Solver() {

	}

	void Solver::Constraint(SharedExpr constraint) {
		smt_engine_.assertFormula(constraint);
		path_constraint_.push_back(constraint);
	}

	bool Solver::IsSat() {
		return smt_engine_.checkSat().isSat();
	}

	interpreter::MetaInt Solver::GetValue(SharedExpr sym_expr) {
		CVC4::Expr res = smt_engine_.getValue(sym_expr);
		CVC4::BitVector val = res.getConst<CVC4::BitVector>();
		interpreter::MetaInt meta_int = interpreter::BitVec_To_MetaInt(val);
		return meta_int;
	}

	void Solver::Print() {
		std::cerr << "PC: \n";
		for (auto i = path_constraint_.begin(); i != path_constraint_.end(); i++) {
			std::cerr << "(" << *i << ")" << "\n\t/\\ ";
		}
		std::cerr << " true \n";
	}

	Type Solver::MkBitVectorType(unsigned size) {
		return expr_manager_.mkBitVectorType(size);
	}

	Type Solver::MkBooleanType() {
		return expr_manager_.booleanType();
	}

	SharedExpr Solver::MkConst(bool val) {
		return expr_manager_.mkConst(val);
	}

	SharedExpr Solver::MkConst(BitVec val) {
		return expr_manager_.mkConst(val);
	}

	SharedExpr Solver::MkConversion__helper(utils::MetaKind kind, unsigned width) {
		switch (kind) {
		case MetaKind::SExt:
			return expr_manager_.mkConst(CVC4::BitVectorSignExtend(width));
		case MetaKind::ZExt:
			return expr_manager_.mkConst(CVC4::BitVectorZeroExtend(width));
		case MetaKind::Trunc:
			return expr_manager_.mkConst(CVC4::BitVectorExtract(width - 1, 0));
		default:
			assert (false and "unexpected");
		}
	}

	SharedExpr Solver::MkConversion(MetaKind kind, unsigned width, SharedExpr target) {
		auto op = MkConversion__helper(kind, width);
		return expr_manager_.mkExpr(op, target);
	}

	SharedExpr Solver::MkVar(Type type) {
		return expr_manager_.mkVar(type);
	}

	SharedExpr Solver::MkExpr(Kind kind, SharedExpr left, SharedExpr right) {
		return expr_manager_.mkExpr(kind, left, right);
	}

	SharedExpr Solver::MkExpr(Kind kind, SharedExpr child1, SharedExpr child2, SharedExpr child3) {
		return expr_manager_.mkExpr(kind, child1, child2, child3);
	}
}















