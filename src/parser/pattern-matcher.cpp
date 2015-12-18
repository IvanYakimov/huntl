#include "pattern-matcher.hpp"
using namespace llvm;

/*
author: Ivan Yakimov
date: 2015
e-mail: ivan.yakimov.research@yandex.ru
*/

void PatternMatcher::DebugInstInfo(const llvm::Instruction &inst) {
# ifdef DBG
	errs() << inst << "\n";
# endif
}

void PatternMatcher::DebugOpList(const llvm::Instruction &inst) {
# ifdef DBG
	for (auto i = 0; i < inst.getNumOperands(); i++) {
		auto type = inst.getOperand(i)->getType();
		errs() << *type << " ";
		if (type->isPointerTy())
			errs() << "ptr";
	}
	errs() << "\n";
# endif
}

// --------------------------------------------------------
// Instruction visitors

void PatternMatcher::visitReturnInst (const ReturnInst &inst) {
	DebugInstInfo(inst);

	Value *ret_val = NULL;

	if (Case (inst, 0, &ret_val))
		HandleReturnInst(inst, ret_val);
	else if (Case (inst, 0))
		HandleReturnInst(inst);
}

void PatternMatcher::visitBranchInst(const BranchInst &inst) {
	DebugInstInfo(inst);

	BasicBlock *iftrue = NULL,
			*iffalse = NULL,
			*jump = NULL;
	Value *cond = NULL;

	if (Case (inst, 0, &cond, &iftrue, &iffalse))
		HandleBranchInst(inst, cond, iftrue, iffalse);
	else if (Case (inst, 0, &jump))
		HandleBranchInst(inst, jump);
	else
		HandleBranchInst(inst);
}

void PatternMatcher::visitICmpInst(const ICmpInst &inst) {
	DebugInstInfo(inst);

	Value *lhs = NULL,
			*rhs = NULL;

	if (Case (inst, 0, &lhs, &rhs))
		HandleICmpInst(inst, lhs, rhs);
	else
		HandleICmpInst(inst);
}

void PatternMatcher::visitAllocaInst (const AllocaInst &inst)
{
	DebugInstInfo(inst);

	Value *allocated = NULL;
	if (Case (inst, 0, &allocated))
		HandleAllocaInst(inst, allocated);
	else
		HandleAllocaInst(inst);
}

void PatternMatcher::visitLoadInst (const LoadInst &inst)
{
	DebugInstInfo(inst);

	Value *ptr= NULL;
	if (Case (inst, 0, &ptr))
		HandleLoadInst(inst, ptr);
	else
		HandleLoadInst(inst);
}

void PatternMatcher::visitStoreInst (const StoreInst &inst)
{
	DebugInstInfo(inst);

	Value *val = NULL;
	Instruction *inst_val= NULL;
	Constant *const_val = NULL;
	Value *ptr = NULL;
	if (Case (inst, 0, &inst_val, &ptr))
		errs() << "inst ptr\n";
	else if (Case (inst, 0, &const_val, &ptr))
		errs() << "const ptr\n";
	else if (Case (inst, 0, &val, &ptr))
		errs() << "val ptr\n";
		//HandleStoreInst(inst, val, ptr);
	else
		InterruptionHandler::Do(new MatchingFailure(inst));

	DebugOpList(inst);
}

//--------------------
// Helper methods
bool PatternMatcher::Case (const Instruction &inst, unsigned i)
{
	if (inst.getNumOperands() != i)
		return false;
	else
		return true;
}

template <typename T, typename... Targs>
bool PatternMatcher::Case (const Instruction &inst, unsigned i, T value, Targs... Fargs)
{
	typedef typename std::remove_pointer<T>::type pV;
	typedef typename std::remove_pointer<pV>::type V;
	auto operand = inst.getOperand (i);
	if (isa<V>(operand)) {
		*value = dyn_cast<V>(operand);
		return true && Case(inst, ++i, Fargs...);
	}
	else
		return false;
}














