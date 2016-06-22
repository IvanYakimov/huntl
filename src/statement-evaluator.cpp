#include "statement-evaluator.hpp"

namespace interpreter {
	using namespace llvm;

	// Return
	void StatementEvaluator::HandleReturnInst (const llvm::Instruction &inst, const llvm::Instruction *ret_inst) {
	}

	void StatementEvaluator::HandleReturnInst (const llvm::Instruction &inst, const llvm::Constant *ret_const) {
		if (ret_const->getType()->isIntegerTy()) {
			auto constant_int = dyn_cast<ConstantInt>(ret_const);
			// Produce constant, use ConstantInt::getSExtValue();
		}
		else
			; // Interpretation failure.
	}

	void StatementEvaluator::HandleReturnInst (const llvm::Instruction &inst) {
	}

	// Branch
	void StatementEvaluator::HandleBranchInst (const llvm::Instruction &inst, const llvm::Value *cond, const llvm::BasicBlock *iftrue, const llvm::BasicBlock *iffalse) {
	}

	void StatementEvaluator::HandleBranchInst (const llvm::Instruction &inst, const llvm::BasicBlock *jump) {
	}

	// BinOp
	void StatementEvaluator::HandleBinOp (const llvm::Instruction &inst, const llvm::Value *lhs, const llvm::Value *rhs) {

	}

	// Cmp
	void StatementEvaluator::HandleICmpInst (const llvm::Instruction &inst, const llvm::Value *lhs, const llvm::Value *rhs) {
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
	void StatementEvaluator::HandleAllocaInst (const llvm::Instruction &inst, const llvm::Value *allocated) {
		// (declare-const <name>)
		// Allocate memory in the current activation record.
		errs() << "var " << inst.getName() << "\n";
	}

	// Load
	void StatementEvaluator::HandleLoadInst (const llvm::Instruction &inst, const llvm::Value *ptr) {
		// (assert (= v e))
		// Load object form ptr
		// Store (associate) object to &inst

	}

	// Store

	void StatementEvaluator::HandleStoreInst (const llvm::Instruction &inst, const llvm::Instruction *instruction, const llvm::Value *ptr) {
		//TODO move to pattern-matcher (?)
		auto name = instruction->getName();
		if (!name.empty()) {
			// Produce new variable
			errs() << *instruction->getType();
			// Store new variable to ptr
		}
		// else
		// Load expr from instruction
		// Store expr to ptr
	}

	void StatementEvaluator::HandleStoreInst (const llvm::Instruction &inst, const llvm::Constant *constant, const llvm::Value *ptr) {
		if (constant->getType()->isIntegerTy()) {
			auto constant_int = dyn_cast<ConstantInt>(constant);
			// Produce new constant
			// Store it to ptr
		}
		else
			; // Interpretation failure
	}
}








