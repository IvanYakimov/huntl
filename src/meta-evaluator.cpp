#include "meta-evaluator.hpp"

namespace interpreter {
	using solver::SharedExpr;
	using memory::Concrete;
	using memory::Symbolic;
	using memory::HolderPtr;
	using memory::IsConcrete;
	using memory::IsSymbolic;
	using utils::MetaKind;
	using llvm::ICmpInst;
	using std::placeholders::_1; using std::placeholders::_2; using std::placeholders::_3; using std::placeholders::_4;

	MetaEvaluator::MetaEvaluator(interpreter::ContextRef context) :
			context_(context),
			concrete_eval_(context),
			symbolic_eval_(context){
	}

	MetaEvaluator::~MetaEvaluator() {
	}

	void MetaEvaluator::BinOp (memory::RamAddress lhs, unsigned op_code, memory::HolderPtr left, memory::HolderPtr right) {
		using OpCode = unsigned;
		ConcreteFunc2<OpCode> concrete_binop = std::bind(&ConcreteEval::BinOp, &concrete_eval_, _1, _2, _3, _4);
		SymbolicFunc2<OpCode> symbolic_binop = std::bind(&SymbolicEval::BinOp, &symbolic_eval_, _1, _2, _3, _4);
		MixedEval2<OpCode>(lhs, op_code, left, right, concrete_binop, symbolic_binop);
	}

	void MetaEvaluator::IntComparison (memory::RamAddress lhs, llvm::ICmpInst::Predicate predicate, memory::HolderPtr left, memory::HolderPtr right) {
		ConcreteFunc2<ICmpInst::Predicate> concrete_comparison = std::bind(&ConcreteEval::IntComparison, &concrete_eval_, _1, _2, _3, _4);
		SymbolicFunc2<ICmpInst::Predicate> symbolic_comparison = std::bind(&SymbolicEval::IntComparison, &symbolic_eval_, _1, _2, _3, _4);
		MixedEval2<ICmpInst::Predicate>(lhs, predicate, left, right, concrete_comparison, symbolic_comparison);
	}

	const llvm::BasicBlock* MetaEvaluator::Branch (memory::HolderPtr condition, const llvm::BasicBlock *iftrue, const llvm::BasicBlock *iffalse) {
		if (memory::IsConcrete(condition)) {
			return concrete_eval_.Branch(memory::GetValue(condition), iftrue, iffalse);
		}
		else if (memory::IsSymbolic(condition))
			return symbolic_eval_.Branch(memory::GetExpr(condition), iftrue, iffalse);
		else
			assert (false and "unexpected behavior");
		return nullptr;
	}

	void MetaEvaluator::Assign (memory::RamAddress lhs, memory::HolderPtr target) {
		if (memory::IsConcrete(target)) {
			concrete_eval_.Assign(lhs, memory::GetValue(target));
		}
		else if (memory::IsSymbolic(target)) {
			symbolic_eval_.Assign(lhs, memory::GetExpr(target));
		}
		else
			assert (false and "unexpected behavior");
	}

	void MetaEvaluator::Conversion (memory::RamAddress lhs, memory::HolderPtr target, utils::MetaKind kind, unsigned new_width) {
		if (memory::IsConcrete(target)) {
			MetaInt value = memory::GetValue(target);
			concrete_eval_.Conversion(lhs, value, kind, new_width);
		}
		else if (memory::IsSymbolic(target)) {
			SharedExpr expr = memory::GetExpr(target);
			symbolic_eval_.Conversion(lhs, expr, kind, new_width);
		}
		else
			assert (false and "unexpected");
	}

	void MetaEvaluator::Return(const llvm::ReturnInst &inst, HolderPtr holder) {
		auto lhs_address = context_.Top()->GetLocation(&inst);
		Assign(lhs_address, holder);
		context_.Top()->RetVal.Set(holder);
		context_.Top()->PC.Set(nullptr);
	}

	void MetaEvaluator::Return(const llvm::ReturnInst &inst) {
		auto undef = memory::Undef::Create();
		context_.Top()->RetVal.Set(undef);
		context_.Top()->PC.Set(nullptr);
	}

	//-------------------------------------------------------------------
	solver::SharedExpr MetaEvaluator::Symbolize(interpreter::MetaIntRef concrete_val) {
		auto bv_val = interpreter::MetaInt_To_BitVec(concrete_val);
		auto c_sym = context_.Solver().MkConst(bv_val);
		return c_sym;
	}

	// Helpers
	template <typename Op>
	void MetaEvaluator::MixedEval2(memory::RamAddress lhs, Op code, memory::HolderPtr left, memory::HolderPtr right, ConcreteFunc2<Op> F, SymbolicFunc2<Op> G) {
		if (IsConcrete(left) and IsConcrete(right)) {
			auto left_val = memory::GetValue(left);
			auto right_val = memory::GetValue(right);
			F(lhs, code, left_val, right_val);
		}
		else if (IsConcrete(left) and IsSymbolic(right)) {
			auto left_sym = Symbolize(memory::GetValue(left));
			auto right_sym = memory::GetExpr(right);
			G(lhs, code, left_sym, right_sym);
		}
		else if (IsSymbolic(left) and IsConcrete(right)) {
			auto left_sym = memory::GetExpr(left);
			auto right_sym = Symbolize(memory::GetValue(right));
			G(lhs, code, left_sym, right_sym);
		}
		else if (IsSymbolic(left) and IsSymbolic(right)) {
			auto left_sym = memory::GetExpr(left);
			auto right_sym = memory::GetExpr(right);
			G(lhs, code, left_sym, right_sym);
		}
		else
			assert (false and "unexpected behavior");
	}
}











