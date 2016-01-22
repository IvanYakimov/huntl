# include "cvc4-engine.hpp"

using namespace CVC4;

namespace solver {
	CVC4Engine::CVC4Engine() {
		smt_engine_ = make_unique<SmtEngine>(&expr_manager_);
		 // ??? Set "Non-linear integer arithmetic with uninterpreted sort and function symbols." logic:
		// This line causes the bug:
		// "SmtEngine: turning off produce-models because unsupported for nonlinear arith
		// Cannot get value when produce-models options is off.Cannot get value when produce-models options is off.f:"
		// smtEngine->setLogic("UFNIA");
		smt_engine_->setOption("incremental", SExpr("true"));
		smt_engine_->setOption("produce-models", SExpr("true"));
		smt_engine_->setOption("rewrite-divk", SExpr("true"));
		symbol_table_.pushScope();
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
		case Result::SAT: return Sat::SAT;
		case Result::UNSAT: return Sat::UNSAT;
		case Result::SAT_UNKNOWN: return Sat::UNKNOWN;
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
	// TODO: extract a template:
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
		//TODO: extract pattern into function
		else if (binop != nullptr) {
			switch (binop->GetOpCode()) {
			case BinaryOperation::OpCode::EQUAL:
				return expr_manager_.mkExpr(CVC4::Kind::EQUAL, Prism(binop->GetLeftChild(), Prism(binop->GetRightChild())));
			case BinaryOperation::OpCode::LESS_THAN:
				return expr_manager_.mkExpr(CVC4::Kind::LT, Prism(binop->GetLeftChild()), Prism(binop->GetRightChild()));
				//TODO:
			}
		}
	}
}















