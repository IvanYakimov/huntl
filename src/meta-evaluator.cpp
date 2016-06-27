#include "meta-evaluator.hpp"

namespace interpreter {
	MetaEvaluator::MetaEvaluator(memory::DisplayPtr display) : display_(display){

	}

	MetaEvaluator::~MetaEvaluator() {

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
