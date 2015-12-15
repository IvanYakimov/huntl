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

void Interpreter::HandleBranchInst (const llvm::Instruction &inst) {

}

  // Cmp
void Interpreter::HandleICmpInst (const llvm::Instruction &inst, const llvm::Value *lhs, const llvm::Value *rhs) {

}


void Interpreter::HandleICmpInst (const llvm::Instruction &inst) {

}

  // Alloca
void Interpreter::HandleAllocaInst (const llvm::Instruction &inst, const llvm::Value *allocated) {

}

void Interpreter::HandleAllocaInst (const llvm::Instruction &inst) {

}

// Load

void Interpreter::HandleLoadInst (const llvm::Instruction &inst, const llvm::Value *ptr) {

}

void Interpreter::HandleLoadInst (const llvm::Instruction &inst) {

}

// Store

void Interpreter::HandleStoreInst (const llvm::Instruction &inst, const llvm::Value *val, const llvm::Value *ptr) {

}

void Interpreter::HandleStoreInst (const llvm::Instruction &inst) {

}










