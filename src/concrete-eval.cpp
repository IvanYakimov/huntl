#include "concrete-eval.hpp"

namespace interpreter {
	using interpreter::MetaInt;
	using interpreter::MetaIntRef;
	using llvm::Instruction;
	using memory::Concrete;
	using interpreter::ContextRef;
	using memory::HolderPtr;

	ConcreteEval::ConcreteEval(ContextRef context) : context_(context) {

	}

	MetaInt ConcreteEval::PerformConcreteBinOp(const llvm::Instruction* inst, MetaIntRef left_val, MetaIntRef right_val) {
		switch (inst->getOpcode()) {
		case Instruction::Add:
			return left_val.operator +(right_val);
		case Instruction::Sub:
			return left_val.operator -(right_val);
		case Instruction::And:
			return left_val.And(right_val);
		case Instruction::LShr:
			return left_val.lshr(right_val);
		}
		assert (false && "not implemented");
	}

	void ConcreteEval::Assign (const llvm::Value* destination, MetaIntRef value) {
		MetaInt new_concrete = value;
		HolderPtr target = Concrete::Create(new_concrete);
		context_.Top()->Store(destination, target);
	}

	void ConcreteEval::BinOp (const llvm::Instruction* inst, MetaIntRef left_val, MetaIntRef right_val) {
		auto result = PerformConcreteBinOp(inst, left_val, right_val);
		auto result_holder = Concrete::Create(result);
		context_.Top()->Store(inst, result_holder);
	}
}
















