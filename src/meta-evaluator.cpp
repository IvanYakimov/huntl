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
			default: assert (false && "not implemented");
			}
			auto result_holder = Concrete::Create(result);
			display_->Store(inst, result_holder);
		}
		else {
			assert (false && "not implemented");
		}
	}

	void MetaEvaluator::Assign(const llvm::Value *destination, const llvm::ConstantInt *target) {
		// Get value of 'constant_int'
		llvm::APInt value = target->getValue();
		auto holder = memory::Concrete::Create(value);
		// Store it to 'ptr'
		display_->Store(destination, holder);
		display_->Print();
	}

	void MetaEvaluator::Assign (const llvm::Value *destination, const llvm::Instruction *target) {
		// Load holder from instruction
		auto loaded_rhs = display_->Load(target);
		// Store holder to ptr
		if (memory::IsConcrete(loaded_rhs)) {
			interpreter::BitVec rhs_val = Object::UpCast<memory::Concrete>(loaded_rhs)->Get();
			auto updated_lhs = memory::Concrete::Create(rhs_val);
			display_->Store(destination, updated_lhs);
		}
		else {
			assert (false && "not impl");
		}
		display_->Print();
	}
}
