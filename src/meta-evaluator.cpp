#include "meta-evaluator.hpp"

namespace interpreter {
	using memory::Concrete;
	using memory::Symbolic;
	using memory::HolderPtr;
	using memory::IsConcrete;
	using memory::IsSymbolic;

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
		if (IsConcrete(left) and IsConcrete(right)) {
			auto left_val = Object::UpCast<Concrete>(left)->Get();
			auto right_val = Object::UpCast<Concrete>(right)->Get();
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











