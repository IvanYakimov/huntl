#include "meta-evaluator.hpp"

namespace interpreter {
	using solver::SharedExpr;
	using memory::Concrete;
	using memory::Symbolic;
	using memory::HolderPtr;
	using memory::IsConcrete;
	using memory::IsSymbolic;
	using std::placeholders::_1; using std::placeholders::_2; using std::placeholders::_3;

	MetaEvaluator::MetaEvaluator(interpreter::ContextRef context) :
			context_(context),
			concrete_eval_(context),
			symbolic_eval_(context){
	}

	MetaEvaluator::~MetaEvaluator() {
	}

	solver::SharedExpr MetaEvaluator::Symbolize(interpreter::MetaIntRef concrete_val) {
		auto bv_val = interpreter::MetaInt_To_BitVec(concrete_val);
		auto c_sym = context_.Solver().MkConst(bv_val);
		return c_sym;
	}

	void MetaEvaluator::BinOp (const llvm::Instruction* inst, memory::HolderPtr left, memory::HolderPtr right) {
		ConcreteFunc2 concrete_binop = std::bind(&ConcreteEval::BinOp, &concrete_eval_, _1, _2, _3);
		SymbolicFunc2 symbolic_binop = std::bind(&SymbolicEval::BinOp, &symbolic_eval_, _1, _2, _3);
		MixedEval2(inst, left, right, concrete_binop, symbolic_binop);
		/*
		if (IsConcrete(left) and IsConcrete(right)) {
			auto left_val = memory::GetValue(left);//Object::UpCast<Concrete>(left)->Get();
			auto right_val = memory::GetValue(right);//Object::UpCast<Concrete>(right)->Get();
			concrete_eval_.BinOp(inst, left_val, right_val);
		}
		else if (IsConcrete(left) and IsSymbolic(right)) {
			auto left_sym = Symbolize(memory::GetValue(left));
			auto right_sym = memory::GetExpr(right);
			symbolic_eval_.BinOp(inst, left_sym, right_sym);
		}
		else if (IsSymbolic(left) and IsConcrete(right)) {
			auto left_sym = memory::GetExpr(left);
			auto right_sym = Symbolize(memory::GetValue(right));
			symbolic_eval_.BinOp(inst, left_sym, right_sym);
		}
		else if (IsSymbolic(left) and IsSymbolic(right)) {
			auto left_sym = memory::GetExpr(left);
			auto right_sym = memory::GetExpr(right);
			symbolic_eval_.BinOp(inst, left_sym, right_sym);
		}
		else
			assert (false and "unexpected behavior");
			*/
	}

	void MetaEvaluator::MixedEval2(const llvm::Instruction* inst, memory::HolderPtr left, memory::HolderPtr right,
					ConcreteFunc2 F, SymbolicFunc2 G) {
		if (IsConcrete(left) and IsConcrete(right)) {
			auto left_val = memory::GetValue(left);//Object::UpCast<Concrete>(left)->Get();
			auto right_val = memory::GetValue(right);//Object::UpCast<Concrete>(right)->Get();
			F(inst, left_val, right_val);
		}
		else if (IsConcrete(left) and IsSymbolic(right)) {
			auto left_sym = Symbolize(memory::GetValue(left));
			auto right_sym = memory::GetExpr(right);
			G(inst, left_sym, right_sym);
		}
		else if (IsSymbolic(left) and IsConcrete(right)) {
			auto left_sym = memory::GetExpr(left);
			auto right_sym = Symbolize(memory::GetValue(right));
			G(inst, left_sym, right_sym);
		}
		else if (IsSymbolic(left) and IsSymbolic(right)) {
			auto left_sym = memory::GetExpr(left);
			auto right_sym = memory::GetExpr(right);
			G(inst, left_sym, right_sym);
		}
		else
			assert (false and "unexpected behavior");
	}

	void ICmpInst (const llvm::Instruction* inst, memory::HolderPtr left, memory::HolderPtr right) {

	}

	void MetaEvaluator::Assign (const llvm::Value *destination, memory::HolderPtr target) {
		if (memory::IsConcrete(target)) {
			concrete_eval_.Assign(destination, memory::GetValue(target));
		}
		else if (memory::IsSymbolic(target)) {
			symbolic_eval_.Assign(destination, memory::GetExpr(target));
		}
		else
			assert (false and "unexpected behavior");
	}
}











