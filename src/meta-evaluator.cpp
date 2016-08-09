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
	using llvm::IntegerType; using llvm::Type; using llvm::dyn_cast; using llvm::isa;

	MetaEvaluator::MetaEvaluator(interpreter::ContextRef context) :
			context_(context),
			concrete_eval_(context),
			symbolic_eval_(context){
	}

	MetaEvaluator::~MetaEvaluator() {
	}

	void MetaEvaluator::BinOp (const llvm::BinaryOperator &binop, memory::HolderPtr left, memory::HolderPtr right) {
		using OpCode = unsigned;
		auto op_code = binop.getOpcode();
		auto lhs_addr = context_.Top()->GetLocation(&binop);
		ConcreteFunc2<OpCode> concrete_binop = std::bind(&ConcreteEval::BinOp, &concrete_eval_, _1, _2, _3, _4);
		SymbolicFunc2<OpCode> symbolic_binop = std::bind(&SymbolicEval::BinOp, &symbolic_eval_, _1, _2, _3, _4);
		MixedEval2<OpCode>(lhs_addr, op_code, left, right, concrete_binop, symbolic_binop);
	}

	void MetaEvaluator::IntComparison (const llvm::ICmpInst &comparison, memory::HolderPtr left, memory::HolderPtr right) {
		auto lhs_address = context_.Top()->GetLocation(&comparison);
		auto predicate = comparison.getPredicate();
		ConcreteFunc2<ICmpInst::Predicate> concrete_comparison = std::bind(&ConcreteEval::IntComparison, &concrete_eval_, _1, _2, _3, _4);
		SymbolicFunc2<ICmpInst::Predicate> symbolic_comparison = std::bind(&SymbolicEval::IntComparison, &symbolic_eval_, _1, _2, _3, _4);
		MixedEval2<ICmpInst::Predicate>(lhs_address, predicate, left, right, concrete_comparison, symbolic_comparison);
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

	void MetaEvaluator::Alloca(const llvm::AllocaInst &lhs, const llvm::Type* allocated_ty) {
		auto lhs_address = context_.Top()->GetLocation(&lhs);
		auto target_address = context_.Top()->Alloca(allocated_ty);
		auto target_address_holder = memory::Concrete::Create(interpreter::MetaInt(memory::Ram::machine_word_bitsize_, target_address));
		Assign(lhs_address, target_address_holder);
		//std::cerr << "alloca addr: " << *target_address_holder << std::endl;
	}

	void MetaEvaluator::Alloca(const llvm::AllocaInst &lhs, memory::HolderPtr initial) {
		auto lhs_address = context_.Top()->GetLocation(&lhs);
		auto target_address = context_.Top()->Alloca(initial);
		auto target_address_holder = memory::Concrete::Create(interpreter::MetaInt(memory::Ram::machine_word_bitsize_, target_address));
		Assign(lhs_address, target_address_holder);
	}

	void MetaEvaluator::Load(const llvm::LoadInst &lhs, memory::HolderPtr ptr_holder) {
		//std::cerr << "load from pointer: " << *ptr_holder << std::endl;
		assert (memory::IsConcrete(ptr_holder));
		MetaIntRef ptr_holder_value = memory::GetValue(ptr_holder);
		// dereferencing
		memory::RamAddress target_address = ptr_holder_value.getZExtValue();
		auto target_holder = context_.Ram().Stack().Read(target_address, memory::Ram::def_align_);
		auto lhs_address = context_.Top()->GetLocation(&lhs);
		Assign(lhs_address, target_holder);
	}

	void MetaEvaluator::Store(const llvm::StoreInst &inst, memory::HolderPtr value_holder, memory::HolderPtr ptr_holder) {
		//std::cerr << "store " << *value_holder << " to ptr: " << *ptr_holder << std::endl;
		assert (memory::IsConcrete(ptr_holder));
		MetaIntRef ptr_concrete_value = memory::GetValue(ptr_holder);
		// dereferencing
		memory::RamAddress target_memory_cell = ptr_concrete_value.getZExtValue();
		Assign(target_memory_cell, value_holder);
	}

	void MetaEvaluator::GetElementPtr(const llvm::GetElementPtrInst &inst, llvm::ArrayType* arr_ty_bound, memory::HolderPtr target_ptr_holder, memory::HolderPtr base_holder, memory::HolderPtr arr_idx_holder) {
		assert (IsConcrete(target_ptr_holder) and IsConcrete(base_holder) and IsConcrete(arr_idx_holder) and "all args must be concrete values");
		IntegerType* el_ty = dyn_cast<IntegerType>(arr_ty_bound->getArrayElementType());
		assert(el_ty != nullptr and "only integer arrays are supported");
		auto el_width = el_ty->getBitWidth();
		assert (el_width % 8 == 0);
		auto el_align = el_width / 8;
		// TODO: boundary checking
		unsigned long base = GetValue(base_holder).getSExtValue();
		unsigned long idx = GetValue(arr_idx_holder).getSExtValue();
		unsigned long ptr = GetValue(target_ptr_holder).getSExtValue();
		assert (base == 0 and "walking throw the pointer is not expected");
		unsigned long result = ptr + idx * el_align;
		assert (sizeof(result) == sizeof(memory::RamAddress));
		HolderPtr result_holder = Concrete::Create(MetaInt(memory::kWordSize, result));
		auto lhs_address = context_.Top()->GetLocation(&inst);
		//std::cerr << "base = " << base << " idx = " << idx << " ptr = " << ptr << " result = " << result << " top-address = " << context_.Ram().Stack().UpperBound() << std::endl;
		//context_.Ram().Stack().Print();
		Assign(lhs_address, result_holder);
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











