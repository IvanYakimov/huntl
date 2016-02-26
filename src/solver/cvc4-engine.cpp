# include "cvc4-engine.hpp"

namespace solver {
	using std::dynamic_pointer_cast;
	using std::logic_error;

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
		//std::cout << "push scope at level " << symbol_table_.getLevel() << std::endl;
	}

	void CVC4Engine::Pop() {
		symbol_table_.popScope();
		//std::cout << "pop scope at level " << symbol_table_.getLevel() << std::endl;
	}

	CVC4Engine::~CVC4Engine() {
		symbol_table_.popScope();
	}

	void CVC4Engine::Assert(ExprPtr expr) {
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

	ValuePtr CVC4Engine::GetValue(ExprPtr expr) throw (std::logic_error) {
		//TODO: check var type! (compare CVC4::Type and solver::Type)
		// The argument must be an instance of a variable
		if (instanceof<Var>(expr)) {
			auto var = std::dynamic_pointer_cast<Var>(expr);
			// Can't return value of unbound variable
			if (not symbol_table_.isBound(var->GetName()))
				return nullptr;
			auto ty = var->GetType();
			// Only integers are supported at the time
			if (instanceof<BasicIntTy>(ty)) {
				auto int_ty = std::dynamic_pointer_cast<BasicIntTy>(ty);
				CVC4::Expr cvcexpr = symbol_table_.lookup(var->GetName());
				CVC4::BitVector btv = cvcexpr.getConst<CVC4::BitVector>();
				CVC4::Integer integer = btv.toInteger();
				uint64_t ulval = integer.getUnsignedLong();
				auto result = GetExprManager()->MkIntVal(int_ty->IsSigned(), int_ty->GetWidth(), ulval);
				return result;
			}
			else throw std::logic_error("only integer type supported");
		}
		else
			throw std::logic_error("incompatible type of expression");
	}

	// private things
	// TODO: refactoring - extract pattern (helper) code
	CVC4::Expr CVC4Engine::Prism(ExprPtr expr) throw(std::logic_error) {
		if (expr == nullptr)
			throw std::logic_error("null not valid");

		// side effect here:
		if (instanceof<Var>(expr)) {
			auto var = dynamic_pointer_cast<Var>(expr);
			CVC4::Expr cvc4var;
			auto var_name = var->GetName();
			//TODO: check var type! (compare CVC4::Type and solver::Type)
			if (symbol_table_.isBound(var_name)) {
				cvc4var = symbol_table_.lookup(var_name);
				//TODO: remove
				//std::cout << "Prism: " << *var << " found " << cvc4var.getType().toString() << " " << cvc4var.toString() << " at level: " << symbol_table_.getLevel() << std::endl;
			}
			else {
				auto ty = var->GetType();
				if (instanceof<BasicIntTy>(ty)) {
					auto int_ty = std::dynamic_pointer_cast<BasicIntTy>(ty);
					auto size = width::to_int(int_ty->GetWidth());
					auto cvc4btv_ty = expr_manager_.mkBitVectorType(size);
					cvc4var = expr_manager_.mkVar(var_name, cvc4btv_ty);
					//TODO: remove of implement as a log-function
					// std::cout << "Prism: " << *var << " creates " << cvc4btv_ty.toString() << " " << cvc4var.toString() << " at level: " << symbol_table_.getLevel() << std::endl;
					symbol_table_.bind(var_name, cvc4var);
				}
				else
					throw std::logic_error("not implemented");
			}
			return cvc4var;
		}
		else if (instanceof<BinOp>(expr)) {
			auto binop = dynamic_pointer_cast<BinOp>(expr);
			//TODO: refactoring
			switch (binop->GetKind()) {
			case solver::Kind::EQ:
				return expr_manager_.mkExpr(CVC4::Kind::EQUAL, Prism(binop->GetLeftChild()), Prism(binop->GetRightChild()));
			}
		}
		else if (instanceof<Const>(expr)) {
			auto cnst = dynamic_pointer_cast<Const>(expr);
			auto val = cnst->GetValue();
			if (instanceof<BasicInt>(val)) {
				auto int_val = dynamic_pointer_cast<BasicInt>(val);
				auto width = int_val->GetWidth();
				auto uval = int_val->GetUInt64();
				return expr_manager_.mkConst(CVC4::BitVector(width::to_int(width), uval));
			}
			else
				throw std::logic_error("not implemented");
		}

		// Expression casting failure
		throw std::logic_error("incompatible type of expression");
	}
}















