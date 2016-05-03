# include "cvc4-engine.hpp"

namespace solver {
	using std::dynamic_pointer_cast;
	using std::logic_error;


	CVC4Engine::CVC4Engine() : smt_engine_(&expr_manager_) {
		smt_engine_.setLogic("QF_BV");
		smt_engine_.setOption("incremental", CVC4::SExpr("true"));
		smt_engine_.setOption("produce-models", CVC4::SExpr("true"));
		smt_engine_.setOption("rewrite-divk", CVC4::SExpr("true"));
	}

	CVC4Engine::~CVC4Engine() throw() {}

	void CVC4Engine::Push() throw() {
		smt_engine_.push();
		symbol_table_.pushScope();
	}

	void CVC4Engine::Pop() throw (ScopeException) {
		try
			{ smt_engine_.pop(); }
		catch (CVC4::ModalException &ex)
			{ throw ScopeException(); }

		if (symbol_table_.getLevel() == 0)
			throw ScopeException();
		else
			symbol_table_.popScope();
	}


	void CVC4Engine::Assert(ExprPtr expr) throw (TypeCheckingException, UnknownException) {
		try {
			smt_engine_.assertFormula(Prism(expr));
		}
		catch (CVC4::TypeCheckingException &ex) {
			throw TypeCheckingException();
		}
		catch (CVC4::Exception &ex) {
			throw UnknownException(ex.what());
		}
	}

	Sat CVC4Engine::CheckSat() {
		try {
			auto result = smt_engine_.checkSat().isSat();
			switch (result) {
				case CVC4::Result::SAT: return Sat::SAT;
				case CVC4::Result::UNSAT: return Sat::UNSAT;
				case CVC4::Result::SAT_UNKNOWN: return Sat::UNKNOWN;
			}
		}
		catch (CVC4::Exception &ex) {
			throw UnknownException(ex.what());
		}
	}

	ValuePtr CVC4Engine::GetValue(ExprPtr expr)
		throw (BindingException, TypeCheckingException, ModelException, ImplementationException, UnknownException) {
		try {
			// One can obtain only value of a variable
			if (instanceof<Var>(expr)) {
				auto var = std::dynamic_pointer_cast<Var>(expr);
				// Can't return value of unbound variable
				if (not symbol_table_.isBound(var->GetName()))
					throw BindingException();
				auto ty = var->GetType();
				// Only integers are supported at the time
				if (instanceof<BasicIntTy>(ty)) {
					auto int_ty = std::dynamic_pointer_cast<BasicIntTy>(ty);
					CVC4::Expr cvc4_expr = symbol_table_.lookup(var->GetName());
					CVC4::Expr cvc4_val = smt_engine_.getValue(cvc4_expr);
					CVC4::BitVector cvc4_btv = cvc4_val.getConst<CVC4::BitVector>();
					if (cvc4_btv.getSize() != to_int(int_ty->GetWidth()))
						throw TypeCheckingException();
					CVC4::Integer cvc4_integer = cvc4_btv.toInteger();
					uint64_t raw_ulval = cvc4_integer.getUnsignedLong();
					auto result = ObjectBuilder::Get()->MkIntVal(int_ty->IsSigned(), int_ty->GetWidth(), raw_ulval);
					return result;
				}
				else throw ImplementationException();
			}
			else
				throw ImplementationException();
		}
		catch (CVC4::ModalException &ex) {
			throw ModelException();
		}
		catch (CVC4::Exception &ex) {
			throw UnknownException(ex.what());
		}
	}

	// private things
	// TODO: refactoring - extract pattern (helper) code
	CVC4::Expr CVC4Engine::Prism(ExprPtr expr) throw(IllegalArgException, CastingException, ImplementationException) {
		if (expr == nullptr)
			throw IllegalArgException();

		// side effect here:
		if (instanceof<Var>(expr)) {
			auto var = dynamic_pointer_cast<Var>(expr);
			CVC4::Expr cvc4var;
			auto var_name = var->GetName();
			if (symbol_table_.isBound(var_name)) {
				cvc4var = symbol_table_.lookup(var_name);
			}
			else {
				auto ty = var->GetType();
				if (instanceof<BasicIntTy>(ty)) {
					auto int_ty = std::dynamic_pointer_cast<BasicIntTy>(ty);
					auto size = to_int(int_ty->GetWidth());
					auto cvc4btv_ty = expr_manager_.mkBitVectorType(size);
					cvc4var = expr_manager_.mkVar(var_name, cvc4btv_ty);
					symbol_table_.bind(var_name, cvc4var);
				}
				else
					throw ImplementationException();
			}
			return cvc4var;
		}
		else if (instanceof<BinOp>(expr)) {
			auto op_map = [&] (solver::Kind kind) -> CVC4::Kind {
				switch (kind) {
				// arithmetic
				case Kind::ADD: return CVC4::Kind::BITVECTOR_PLUS;
				case Kind::SUB: return CVC4::Kind::BITVECTOR_SUB;
				case Kind::MUL: return CVC4::Kind::BITVECTOR_MULT;
				//TODO: what is SDIV_TOTAL?
				case Kind::SDIV: return CVC4::Kind::BITVECTOR_SDIV;
				case Kind::SREM: return CVC4::Kind::BITVECTOR_SREM;
				//TODO: what is UDIV_TOTAL?
				case Kind::UDIV: return CVC4::Kind::BITVECTOR_UDIV;
				case Kind::UREM: return CVC4::Kind::BITVECTOR_UREM;
				case Kind::SHL: return CVC4::Kind::BITVECTOR_SHL;
				case Kind::LSHR: return CVC4::Kind::BITVECTOR_LSHR;
				case Kind::ASHR: return CVC4::Kind::BITVECTOR_ASHR;
				// bitwise
				case Kind::AND: return CVC4::Kind::BITVECTOR_AND;
				case Kind::OR: return CVC4::Kind::BITVECTOR_OR;
				case Kind::XOR: return CVC4::Kind::BITVECTOR_XOR;
				// comparisons
				case Kind::EQUAL: return CVC4::Kind::EQUAL;
				case Kind::DISTINCT: return CVC4::Kind::DISTINCT;
				case Kind::UGT: return CVC4::Kind::BITVECTOR_UGT;
				case Kind::UGE: return CVC4::Kind::BITVECTOR_UGE;
				case Kind::ULT: return CVC4::Kind::BITVECTOR_ULT;
				case Kind::ULE: return CVC4::Kind::BITVECTOR_ULE;
				case Kind::SGT: return CVC4::Kind::BITVECTOR_SGT;
				case Kind::SGE: return CVC4::Kind::BITVECTOR_SGE;
				case Kind::SLT: return CVC4::Kind::BITVECTOR_SLT;
				case Kind::SLE: return CVC4::Kind::BITVECTOR_SLE;
				}
			};

			auto binop = dynamic_pointer_cast<BinOp>(expr);
			CVC4::Expr cvc4_binop = expr_manager_.mkExpr(op_map(binop->GetKind()),
					Prism(binop->GetLeftChild()), Prism(binop->GetRightChild()));
			return cvc4_binop;
		}
		else if (instanceof<Const>(expr)) {
			auto cnst = dynamic_pointer_cast<Const>(expr);
			auto val = cnst->GetValue();
			if (instanceof<BasicInt>(val)) {
				auto int_val = dynamic_pointer_cast<BasicInt>(val);
				auto width = int_val->GetWidth();
				auto raw_ulval = int_val->GetUInt64();
				return expr_manager_.mkConst(CVC4::BitVector(to_int(width), raw_ulval));
			}
			else
				throw ImplementationException();
		}

		// Expression casting failure
		throw CastingException();
	}
}















