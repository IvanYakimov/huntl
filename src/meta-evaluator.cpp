#include "meta-evaluator.hpp"

namespace interpreter {
	MetaEvaluator::MetaEvaluator() {

	}

	MetaEvaluator::~MetaEvaluator() {

	}

	void MetaEvaluator::Assign(const llvm::Value *destination, const llvm::ConstantInt *target) {
		// Get value of 'constant_int'
		auto display = utils::GetInstance<memory::Display>();
		llvm::APInt value = target->getValue();
		auto holder = memory::Concrete::Create(value);
		// Store it to 'ptr'
		display->Store(destination, holder);
		display->Print();
	}

	void MetaEvaluator::Assign (const llvm::Value *destination, const llvm::Instruction *target) {
		// Load holder from instruction
		auto display = utils::GetInstance<memory::Display>();
		auto loaded_rhs = display->Load(target);
		// Store holder to ptr
		if (memory::IsConcrete(loaded_rhs)) {
			interpreter::BitVec rhs_val = Object::UpCast<memory::Concrete>(loaded_rhs)->Get();
			auto updated_lhs = memory::Concrete::Create(rhs_val);
			display->Store(destination, updated_lhs);
		}
		else {
			assert (false && "not impl");
		}
		display->Print();
	}
}
