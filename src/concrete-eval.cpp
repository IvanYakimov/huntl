#include "concrete-eval.hpp"

namespace interpreter {
	using interpreter::MetaInt;
	using interpreter::MetaIntRef;
	using llvm::Instruction;
	using memory::Concrete;
	using interpreter::ContextRef;
	using memory::HolderPtr;
	using llvm::ICmpInst;

	ConcreteEval::ConcreteEval(ContextRef context) : context_(context), True(1,1,false), False(1,0,false) {

	}

	MetaInt ConcreteEval::BinOp__helper(const llvm::Instruction* inst, MetaIntRef left_val, MetaIntRef right_val) {
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

	bool ConcreteEval::IntComparison__helper(const llvm::ICmpInst* inst, MetaIntRef left_val, MetaIntRef right_val) {
		switch (inst->getPredicate()) {
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

	MetaInt ConcreteEval::Conversion__helper (MetaIntRef rhs, MetaKind kind, unsigned width) {
		switch (kind) {
		case MetaKind::ZExt:
			return rhs.zext(width);
		case MetaKind::SExt:
			return rhs.sext(width);
		case MetaKind::Trunc:
			return rhs.trunc(width);
		default:
			assert (false and "fail to convert");
		}
	}

	void ConcreteEval::Assign (const llvm::Value* destination, MetaIntRef value) {
		MetaInt new_concrete = value;
		HolderPtr target = Concrete::Create(new_concrete);
		context_.Top()->Store(destination, target);
	}

	void ConcreteEval::Conversion (const llvm::Instruction* lhs, interpreter::MetaIntRef rhs, MetaKind kind, unsigned width) {
		auto result = Conversion__helper(rhs, kind, width);
		Assign(lhs, result);
	}

	void ConcreteEval::BinOp (const llvm::Instruction* inst, MetaIntRef left_val, MetaIntRef right_val) {
		auto result = BinOp__helper(inst, left_val, right_val);
		Assign(inst, result);
	}

	void ConcreteEval::IntComparison(const llvm::Instruction* inst, interpreter::MetaIntRef left_val, interpreter::MetaIntRef right_val) {
		const llvm::ICmpInst *icmp_inst = llvm::dyn_cast<llvm::ICmpInst>(inst);
		bool result = IntComparison__helper(icmp_inst, left_val, right_val);
		MetaInt casted_result;
		if (result == true)
			casted_result = True;
		else
			casted_result = False;
		Assign(inst, casted_result);
	}

	const llvm::BasicBlock* ConcreteEval::Branch(const llvm::Instruction *inst, interpreter::MetaIntRef condition, const llvm::BasicBlock *iftrue, const llvm::BasicBlock *iffalse) {
		if (condition == True) {
			return iftrue;
		}
		else if (condition == False) {
			return iffalse;
		}
		else
			assert (false and "unexpected conditional");
		return nullptr;
	}
}
















