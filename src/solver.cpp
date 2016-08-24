#include "solver.hpp"

namespace solver {
	using utils::MetaKind;

	Solver::Solver() : expr_manager_(), smt_engine_(&expr_manager_), symbol_table_() {
		smt_engine_.setOption("incremental", CVC4::SExpr("true"));
		smt_engine_.setOption("produce-models", CVC4::SExpr("true"));
		smt_engine_.setOption("rewrite-divk", CVC4::SExpr("true"));
		smt_engine_.setLogic("QF_BV");
	}

	Solver::~Solver() {

	}

	void Solver::Constraint(SharedExpr constraint) {
		smt_engine_.assertFormula(constraint);
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
		assert (false and "not implemented");
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

	SharedExpr Solver::MkConversion__helper(utils::MetaKind kind, unsigned arg) {
		switch (kind) {
		case MetaKind::SExt:
			return expr_manager_.mkConst(CVC4::BitVectorSignExtend(arg));
		case MetaKind::ZExt:
			return expr_manager_.mkConst(CVC4::BitVectorZeroExtend(arg));
		case MetaKind::Trunc:
			return expr_manager_.mkConst(CVC4::BitVectorExtract(arg - 1, 0));
		default:
			assert (false and "unexpected");
		}
	}

	SharedExpr Solver::MkConversion(MetaKind kind, unsigned new_width, SharedExpr target) {
		CVC4::BitVectorType target_type = target.getType();
		auto target_width = target_type.getSize();
		SharedExpr op;
		if (kind == MetaKind::SExt or kind == MetaKind::ZExt) {
			auto increment = new_width - target_width;
			assert (increment > 0 and increment <= 64);
			op = MkConversion__helper(kind, increment);
		}
		else if (kind == MetaKind::Trunc) {
			assert (target_width > new_width);
			op = MkConversion__helper(kind, new_width);
		}
		else
			assert (false and "unexpected");

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

	void Solver::Push() {
		smt_engine_.push();
	}

	void Solver::Pop() {
		smt_engine_.pop();
	}
}















