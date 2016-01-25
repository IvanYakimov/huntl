# include "cvc4-engine.hpp"

namespace solver {
	CVC4Engine::CVC4Engine() {
		smt_engine_ = make_unique<CVC4::SmtEngine>(&expr_manager_);
		 // ??? Set "Non-linear integer arithmetic with uninterpreted sort and function symbols." logic:
		// This line causes the bug:
		// "SmtEngine: turning off produce-models because unsupported for nonlinear arith
		// Cannot get value when produce-models options is off.Cannot get value when produce-models options is off.f:"
		// smtEngine->setLogic("UFNIA");
		smt_engine_->setOption("incremental", CVC4::SExpr("true"));
		smt_engine_->setOption("produce-models", CVC4::SExpr("true"));
		smt_engine_->setOption("rewrite-divk", CVC4::SExpr("true"));
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
		smt_engine_->assertFormula(Prism(expr));
	}

	Sat CVC4Engine::CheckSat() {
		auto result = smt_engine_->checkSat().isSat();
		switch (result) {
		case CVC4::Result::SAT: return Sat::SAT;
		case CVC4::Result::UNSAT: return Sat::UNSAT;
		case CVC4::Result::SAT_UNKNOWN: return Sat::UNKNOWN;
		}
	}

	std::int32_t CVC4Engine::GetValue(SharedExprPtr expr) {
		//TODO:
		// comment: at the moment the implementation of the
		// getConst<CVC4::Integer> function hasn't been found
		auto var = dynamic_cast<Variable*>(&*expr);
		auto name = symbol_table_.lookup(var->GetName());
		auto value = smt_engine_->getValue(name).getConst<CVC4::Rational>();
		return static_cast<std::int32_t>(value.getNumerator().getLong());
	}

	// private things
	// TODO: refactoring - extract pattern code
	CVC4::Expr CVC4Engine::Prism(SharedExprPtr expr) {
		auto var = dynamic_cast<Variable*>(&*expr);
		auto binop = dynamic_cast<BinaryOperation*>(&*expr);
		auto cnst = dynamic_cast<ConstantI32*>(&*expr);
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
			switch (binop->GetOpCode()) {
			case solver::Kind::ADD:
				return expr_manager_.mkExpr(CVC4::Kind::BITVECTOR_PLUS, Prism(binop->GetLeftChild()), Prism(binop->GetRightChild()));
			case solver::Kind::SUB:
				return expr_manager_.mkExpr(CVC4::Kind::BITVECTOR_SUB, Prism(binop->GetLeftChild()), Prism(binop->GetRightChild()));
			case solver::Kind::MUL:
				return expr_manager_.mkExpr(CVC4::Kind::BITVECTOR_MULT, Prism(binop->GetLeftChild()), Prism(binop->GetRightChild()));
			case solver::Kind::EQUAL:
				return expr_manager_.mkExpr(CVC4::Kind::EQUAL, Prism(binop->GetLeftChild()), Prism(binop->GetRightChild()));
			}
		}
		else if (cnst != nullptr) {
			auto val = cnst->GetValue();
			unsigned long place;
			memcpy(&place, &val, sizeof(unsigned long));
			expr_manager_.mkConst(CVC4::BitVector(sizeof(val), place));
		}
		// default:
		throw std::bad_cast();
	}
}















