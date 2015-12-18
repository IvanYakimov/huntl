# include "interpreter.hpp"

// Return
void Interpreter::HandleReturnInst (const llvm::Instruction &inst, const llvm::Value *ret_val) {

}

void Interpreter::HandleReturnInst (const llvm::Instruction &inst) {

}

// Branch
void Interpreter::HandleBranchInst (const llvm::Instruction &inst, const llvm::Value *cond, const llvm::BasicBlock *iftrue, const llvm::BasicBlock *iffalse) {

}

void Interpreter::HandleBranchInst (const llvm::Instruction &inst, const llvm::BasicBlock *jump) {

}

// Cmp
void Interpreter::HandleICmpInst (const llvm::Instruction &inst, const llvm::Value *lhs, const llvm::Value *rhs) {

}


// Alloca
void Interpreter::HandleAllocaInst (const llvm::Instruction &inst, const llvm::Value *allocated) {

}

// Load
void Interpreter::HandleLoadInst (const llvm::Instruction &inst, const llvm::Value *ptr) {

}

// Store
void Interpreter::HandleStoreInst (const llvm::Instruction &inst, const llvm::Value *val, const llvm::Value *ptr) {

}

void Interpreter::HandleStoreInst (const llvm::Instruction &inst, const llvm::Instruction *instruction, const llvm::Value *ptr) {

}

void Interpreter::HandleStoreInst (const llvm::Instruction &inst, const llvm::Constant *constant, const llvm::Value *ptr) {

}








