#include "meta-evaluator.hpp"

namespace interpreter {
	using memory::Concrete;
	using memory::Symbolic;
	using memory::HolderPtr;

	MetaEvaluator::MetaEvaluator(memory::DisplayPtr display) : display_(display){

	}

	MetaEvaluator::~MetaEvaluator() {

	}

	void MetaEvaluator::BinOp (const llvm::Instruction* inst, memory::HolderPtr left, memory::HolderPtr right) {
		if (memory::IsConcrete(left) and memory::IsConcrete(right)) {
			interpreter::BitVec left_val = Object::UpCast<Concrete>(left)->Get();
			interpreter::BitVec right_val = Object::UpCast<Concrete>(right)->Get();
			interpreter::BitVec result;
			switch (inst->getOpcode()) {
			case llvm::Instruction::Add:
				result = left_val.operator +(right_val);
				break;
			default: assert (false && "this binary operator not implemented");
			}
			auto result_holder = Concrete::Create(result);
			display_->Store(inst, result_holder);
		}
		else {
			assert (false && "not implemented");
		}
	}

	void MetaEvaluator::Assign (const llvm::Value *destination, memory::HolderPtr target) {
		if (memory::IsConcrete(target)) {
			//interpreter::BitVec rhs_val = Object::UpCast<memory::Concrete>(loaded_rhs)->Get();
			//auto updated_lhs = memory::Concrete::Create(rhs_val);
			display_->Store(destination, target);
		}
		else
			assert (false && "not implemented");
	}
}
