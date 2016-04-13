#include "matcher-stub.hpp"

namespace interpreter {
	using namespace llvm;

	// Return
	void MatcherStub::HandleReturnInst (const llvm::Instruction &inst, const llvm::Instruction *ret_inst) {
		llvm::errs() << "[ret inst]\n";
		FAIL();
	}

	void MatcherStub::HandleReturnInst (const llvm::Instruction &inst, const llvm::Constant *ret_const) {
		llvm::errs() << "[ret const]\n";
		ASSERT_TRUE(isa<Instruction>(inst));
		ASSERT_TRUE(isa<Constant>(ret_const));
	}

	void MatcherStub::HandleReturnInst (const llvm::Instruction &inst, const llvm::Value *ret_val) {
		llvm::errs() << "[ret val]\n";
		FAIL();
	}

	void MatcherStub::HandleReturnInst (const llvm::Instruction &inst) {
		llvm::errs() << "[ret void]\n";
		ASSERT_TRUE(isa<Instruction>(inst));
		FAIL();
	}

	// Branch
	void MatcherStub::HandleBranchInst (const llvm::Instruction &inst,
		  const llvm::Value *cond, const llvm::BasicBlock *iftrue, const llvm::BasicBlock *iffalse) {
		FAIL();
	}

	void MatcherStub::HandleBranchInst (const llvm::Instruction &inst, const llvm::BasicBlock *jump) {
		FAIL();
	}

	// Cmp
	void MatcherStub::HandleICmpInst (const llvm::Instruction &inst, const llvm::Value *lhs, const llvm::Value *rhs) {
		FAIL();
	}

	// Alloca
	void MatcherStub::HandleAllocaInst (const llvm::Instruction &inst, const llvm::Value *allocated) {
		FAIL();
	}

	// Load
	void MatcherStub::HandleLoadInst (const llvm::Instruction &inst, const llvm::Value *ptr) {
		FAIL();
	}

	// Store
	void MatcherStub::HandleStoreInst (const llvm::Instruction &inst, const llvm::Value *val, const llvm::Value *ptr) {
		FAIL();
	}

	void MatcherStub::HandleStoreInst (const llvm::Instruction &inst, const llvm::Instruction *instruction, const llvm::Value *ptr) {
		FAIL();
	}

	void MatcherStub::HandleStoreInst (const llvm::Instruction &inst, const llvm::Constant *constant, const llvm::Value *ptr) {
		FAIL();
	}
}




















