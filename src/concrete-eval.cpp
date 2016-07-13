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
		case Instruction::Mul:
			return left_val.operator *(right_val);
		case Instruction::SDiv:
			return left_val.sdiv(right_val);
		case Instruction::SRem:
			return left_val.srem(right_val);
		case Instruction::UDiv:
			return left_val.udiv(right_val);
		case Instruction::URem:
			return left_val.urem(right_val);
		case Instruction::And:
			return left_val.And(right_val);
		case Instruction::Or:
			return left_val.Or(right_val);
		case Instruction::Xor:
			return left_val.Xor(right_val);
		case Instruction::Shl:
			return left_val.shl(right_val);
		case Instruction::AShr:
			return left_val.ashr(right_val);
		case Instruction::LShr:
			return left_val.lshr(right_val);
		}
		assert (false && "not implemented");
	}

	bool ConcreteEval::PerformConcreteICmpInst(const llvm::ICmpInst* inst, MetaIntRef left_val, MetaIntRef right_val) {
			switch (inst->getOpcode()) {
			case llvm::ICmpInst::ICMP_EQ:
				return left_val.eq(right_val);
			case llvm::ICmpInst::ICMP_NE:
				return left_val.ne(right_val);
			case llvm::ICmpInst::ICMP_SGE:
				return left_val.sge(right_val);
			case llvm::ICmpInst::ICMP_SGT:
				return left_val.sgt(right_val);
			case llvm::ICmpInst::ICMP_SLE:
				return left_val.sle(right_val);
			case llvm::ICmpInst::ICMP_SLT:
				return left_val.slt(right_val);
			case llvm::ICmpInst::ICMP_UGE:
				return left_val.uge(right_val);
			case llvm::ICmpInst::ICMP_UGT:
				return left_val.ugt(right_val);
			case llvm::ICmpInst::ICMP_ULE:
				return left_val.ule(right_val);
			case llvm::ICmpInst::ICMP_ULT:
				return left_val.ult(right_val);
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

	void ConcreteEval::ICmpInst(const llvm::Instruction* inst, interpreter::MetaIntRef left_val, interpreter::MetaIntRef right_val) {
	}
}
















