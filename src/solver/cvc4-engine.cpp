# include "cvc4-engine.hpp"

namespace solver {
	CVC4Engine::CVC4Engine() : smt_engine_(&expr_manager_) {
		 // ??? Set "Non-linear integer arithmetic with uninterpreted sort and function symbols." logic:
		// This line causes the bug:
		// "SmtEngine: turning off produce-models because unsupported for nonlinear arith
		// Cannot get value when produce-models options is off.Cannot get value when produce-models options is off.f:"
		// smtEngine->setLogic("UFNIA");
		smt_engine_.setOption("incremental", CVC4::SExpr("true"));
		smt_engine_.setOption("produce-models", CVC4::SExpr("true"));
		smt_engine_.setOption("rewrite-divk", CVC4::SExpr("true"));
		btv32_ = expr_manager_.mkBitVectorType(32);
		symbol_table_.pushScope();
	}

	void CVC4Engine::Push() {
		symbol_table_.pushScope();
	}

	void CVC4Engine::Pop() {
		symbol_table_.popScope();
	}

	CVC4Engine::~CVC4Engine() {
		symbol_table_.popScope();
	}

	void CVC4Engine::Assert(SharedExprPtr expr) {
		smt_engine_.assertFormula(Prism(expr));
	}

	Sat CVC4Engine::CheckSat() {
		auto result = smt_engine_.checkSat().isSat();
		switch (result) {
		case CVC4::Result::SAT: return Sat::SAT;
		case CVC4::Result::UNSAT: return Sat::UNSAT;
		case CVC4::Result::SAT_UNKNOWN: return Sat::UNKNOWN;
		}
	}

	std::int32_t CVC4Engine::GetValue(SharedExprPtr expr) {
		auto var = std::dynamic_pointer_cast<Var>(expr);
		if (!var)
			throw std::bad_cast();
		auto cvcexpr = symbol_table_.lookup(var->GetName());
		auto btv_const = cvcexpr.getConst<CVC4::BitVector>();
		return GetValue(btv_const);
	}

	std::int32_t CVC4Engine::GetValue(CVC4::BitVector btv_const) {
		auto integer_const = btv_const.toInteger();
		auto long_val = integer_const.getLong();
		std::int32_t int_val = long_val bitand (compl 0);
		return int_val;
	}

	// private things
	// TODO: refactoring - extract pattern (helper) code
	CVC4::Expr CVC4Engine::Prism(SharedExprPtr expr) {
		auto var = std::dynamic_pointer_cast<Var>(expr);
		auto binop = std::dynamic_pointer_cast<BinOp>(expr);
		auto cnst = std::dynamic_pointer_cast<ConstI32>(expr);
		// side effect here:
		if (var != nullptr) {
			CVC4::Expr var_expr;
			auto var_name = var->GetName();
			if (symbol_table_.isBound(var_name)) {
				var_expr = symbol_table_.lookup(var_name);
			}
			else {
				var_expr = expr_manager_.mkVar(var_name, expr_manager_.integerType());
				symbol_table_.bind(var_name, var_expr);
			}
			return var_expr;
		}
		else if (binop != nullptr) {
			//TODO: refactoring
			switch (binop->GetKind()) {
			case solver::Kind::EQ:
				return expr_manager_.mkExpr(CVC4::Kind::EQUAL, Prism(binop->GetLeftChild()), Prism(binop->GetRightChild()));
			}
		}
		else if (cnst != nullptr) {
			auto val = cnst->GetValue();
			//TODO verify bitwise operation usage
			unsigned int uval = val bitand (compl 0);
			return expr_manager_.mkConst(CVC4::BitVector(32, uval));
		}

		// Expression casting failure
		throw std::invalid_argument("shared expression casting failure");
	}
}















