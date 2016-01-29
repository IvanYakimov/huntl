# include "interpreter.hpp"

using namespace llvm;
using namespace solver;

//TODO interruption handling (replace interruptions by exceptions)
void Interpreter::DebugExprInfo(SharedExpr expr) {
# ifdef DBG
	if (expr)
		errs() << "> " << expr->ToString() << "\n";
	else
		errs() << "> void" << "\n";
# endif
}

// Return
void Interpreter::HandleReturnInst (const llvm::Instruction &inst, const llvm::Instruction *ret_inst) {
	auto expr = memory_.Load(ret_inst);

	DebugExprInfo(expr);
}

void Interpreter::HandleReturnInst (const llvm::Instruction &inst, const llvm::Constant *ret_const) {
	if (ret_const->getType()->isIntegerTy()) {
		auto constant_int = dyn_cast<ConstantInt>(ret_const);
		auto expr = expr_factory_.ProduceConstantI32(constant_int->getSExtValue());

		DebugExprInfo(expr);
	}
	else
		InterruptionHandler::Do(new InterpretationFailure(inst));
}

void Interpreter::HandleReturnInst (const llvm::Instruction &inst, const llvm::Value *ret_val) {

}

void Interpreter::HandleReturnInst (const llvm::Instruction &inst) {
	DebugExprInfo(NULL);
}

// Branch
void Interpreter::HandleBranchInst (const llvm::Instruction &inst, const llvm::Value *cond, const llvm::BasicBlock *iftrue, const llvm::BasicBlock *iffalse) {

}

void Interpreter::HandleBranchInst (const llvm::Instruction &inst, const llvm::BasicBlock *jump) {

}

// Cmp
void Interpreter::HandleICmpInst (const llvm::Instruction &inst, const llvm::Value *lhs, const llvm::Value *rhs) {
	auto get_op = [](const llvm::Instruction &inst) {
		auto icmp_inst = dyn_cast<ICmpInst>(&inst);
		switch (icmp_inst->getPredicate()) {
			case CmpInst::Predicate::ICMP_SLT: return solver::BinOp::LESS_THAN;
			default: InterruptionHandler::Do(new InterpretationFailure(inst));
		};
	};

	auto left = memory_.Load(lhs);
	auto right = memory_.Load(rhs);
	auto expr = expr_factory_.ProduceBinaryOperation(left, right, get_op(inst));

	DebugExprInfo(expr);
}

// Alloca
void Interpreter::HandleAllocaInst (const llvm::Instruction &inst, const llvm::Value *allocated) {
	memory_.Alloca(allocated);
}

// Load
void Interpreter::HandleLoadInst (const llvm::Instruction &inst, const llvm::Value *ptr) {
	auto expr = memory_.Load(ptr);
	memory_.Store(&inst, expr);
}

// Store
void Interpreter::HandleStoreInst (const llvm::Instruction &inst, const llvm::Value *val, const llvm::Value *ptr) {
	//TODO move to pattern-matcher (?)
	auto name = val->getName();
	if (!name.empty())
		memory_.Store(ptr, expr_factory_.MkVar(name.str()));
	else
		InterruptionHandler::Do(new InterpretationFailure(inst));
}

void Interpreter::HandleStoreInst (const llvm::Instruction &inst, const llvm::Instruction *instruction, const llvm::Value *ptr) {
	auto expr = memory_.Load(instruction);
	memory_.Store(ptr, expr);
}

void Interpreter::HandleStoreInst (const llvm::Instruction &inst, const llvm::Constant *constant, const llvm::Value *ptr) {
	if (constant->getType()->isIntegerTy()) {
		auto constant_int = dyn_cast<ConstantInt>(constant);
		memory_.Store(ptr, expr_factory_.ProduceConstantI32(constant_int->getSExtValue()));
	}
}








