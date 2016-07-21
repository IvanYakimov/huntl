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
	}

	void MetaEvaluator::MixedEval2(const llvm::Instruction* inst, memory::HolderPtr left, memory::HolderPtr right,
					ConcreteFunc2 F, SymbolicFunc2 G) {
		if (IsConcrete(left) and IsConcrete(right)) {
			auto left_val = memory::GetValue(left);
			auto right_val = memory::GetValue(right);
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

	void MetaEvaluator::IntComparison (const llvm::Instruction* inst, memory::HolderPtr left, memory::HolderPtr right) {
		ConcreteFunc2 concrete_comparison = std::bind(&ConcreteEval::IntComparison, &concrete_eval_, _1, _2, _3);
		SymbolicFunc2 symbolic_comparison = std::bind(&SymbolicEval::IntComparison, &symbolic_eval_, _1, _2, _3);
		MixedEval2(inst, left, right, concrete_comparison, symbolic_comparison);
	}

	const llvm::BasicBlock* MetaEvaluator::Branch (const llvm::Instruction *inst, memory::HolderPtr condition,
			const llvm::BasicBlock *iftrue, const llvm::BasicBlock *iffalse) {
		if (memory::IsConcrete(condition)) {
			return concrete_eval_.Branch(inst, memory::GetValue(condition), iftrue, iffalse);
		}
		else if (memory::IsSymbolic(condition))
			return symbolic_eval_.Branch(inst, memory::GetExpr(condition), iftrue, iffalse);
		else
			assert (false and "unexpected behavior");
		return nullptr;
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

	void MetaEvaluator::Dereferencing (const llvm::Value* lhs, memory::HolderPtr ptr_holder) {
		if (memory::IsConcrete(ptr_holder)) {
			auto deref_holder = context_.Top()->Dereference(ptr_holder);
			if (memory::IsConcrete(deref_holder)) {
				MetaIntRef deref_concrete = memory::GetValue(deref_holder);
				concrete_eval_.Assign(lhs, deref_concrete);
			}
			else if (memory::IsSymbolic(deref_holder)) {
				//assert (false and "not implemented");
				SharedExpr deref_sym = memory::GetExpr(deref_holder);
				symbolic_eval_.Assign(lhs, deref_sym);
			}
			else
				assert (false and "unexpected");
		}
		else if (memory::IsSymbolic(ptr_holder)) {
			assert (false and "not implemented");
		}
		else assert (false and "unexpected behavior");
	}

	void MetaEvaluator::Addressing (const llvm::Value* lhs, memory::HolderPtr addr_holder) {
		if (memory::IsConcrete(addr_holder)) {
			MetaIntRef addr_concrete = memory::GetValue(addr_holder);
			concrete_eval_.Assign(lhs, addr_concrete);
		}
		else if (memory::IsSymbolic(addr_holder)) {
			assert (false and "not implemented");
		}
		else
			assert (false and "unexpected");
	}

	void MetaEvaluator::Conversion (const llvm::Instruction* lhs, memory::HolderPtr rhs, MetaKind kind, unsigned width) {
		if (memory::IsConcrete(rhs)) {
			MetaInt value = memory::GetValue(rhs);
			concrete_eval_.Conversion(lhs, value, kind, width);
		}
		else if (memory::IsSymbolic(rhs)) {
			assert (false and "not implemented");
		}
		else
			assert (false and "unexpected");
	}
}











