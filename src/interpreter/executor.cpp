#include "executor.hpp"

namespace interpreter {
	using namespace llvm;

	// Return
	void Executor::HandleReturnInst (const llvm::Instruction &inst, const llvm::Instruction *ret_inst) {
	}

	void Executor::HandleReturnInst (const llvm::Instruction &inst, const llvm::Constant *ret_const) {
		if (ret_const->getType()->isIntegerTy()) {
			auto constant_int = dyn_cast<ConstantInt>(ret_const);
			// Produce constant, use ConstantInt::getSExtValue();
		}
		else
			; // Interpretation failure.
	}

	void Executor::HandleReturnInst (const llvm::Instruction &inst, const llvm::Value *ret_val) {
	}

	void Executor::HandleReturnInst (const llvm::Instruction &inst) {
	}

	// Branch
	void Executor::HandleBranchInst (const llvm::Instruction &inst, const llvm::Value *cond, const llvm::BasicBlock *iftrue, const llvm::BasicBlock *iffalse) {
	}

	void Executor::HandleBranchInst (const llvm::Instruction &inst, const llvm::BasicBlock *jump) {
	}

	// BinOp
	void Executor::HandleBinOp (const llvm::Instruction &inst, const llvm::Value *lhs, const llvm::Value *rhs) {

	}

	// Cmp
	void Executor::HandleICmpInst (const llvm::Instruction &inst, const llvm::Value *lhs, const llvm::Value *rhs) {
		auto get_op = [](const llvm::Instruction &inst) {
			auto icmp_inst = dyn_cast<ICmpInst>(&inst);
			switch (icmp_inst->getPredicate()) {
				//case CmpInst::Predicate::ICMP_SLT: return solver::BinOp::LESS_THAN;
				//default: InterruptionHandler::Do(new InterpretationFailure(inst));
			};
		};

		// Load left and right args.
		// Produce expression, use get_op, defined above
	}

	// Alloca
	void Executor::HandleAllocaInst (const llvm::Instruction &inst, const llvm::Value *allocated) {
		// Allocate memory in the current activation record.
		display_->Alloc(&inst);
	}

	// Load
	void Executor::HandleLoadInst (const llvm::Instruction &inst, const llvm::Value *ptr) {
		// Load object form ptr
		auto obj = display_->Load(ptr);
		// Store (associate) object to &inst
		display_->Store(&inst, obj);
	}

	// Store
	void Executor::HandleStoreInst (const llvm::Instruction &inst, const llvm::Value *val, const llvm::Value *ptr) {
		//TODO move to pattern-matcher (?)
		auto name = val->getName();
		if (!name.empty()) {
			// Produce new variable
			// Store new variable to ptr
		}
		else
			; // Interpretation Failure
	}

	void Executor::HandleStoreInst (const llvm::Instruction &inst, const llvm::Instruction *instruction, const llvm::Value *ptr) {
		// Load expr from instruction
		// Store expr to ptr
	}

	void Executor::HandleStoreInst (const llvm::Instruction &inst, const llvm::Constant *constant, const llvm::Value *ptr) {
		if (constant->getType()->isIntegerTy()) {
			auto constant_int = dyn_cast<ConstantInt>(constant);
			// Produce new constant
			// Store it to ptr
		}
		else
			; // Interpretation failure
	}
}








