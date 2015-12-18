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
	else
		InterruptionHandler::Do(new MatchingFailure(inst));
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
		InterruptionHandler::Do(new MatchingFailure(inst));
}

void PatternMatcher::visitICmpInst(const ICmpInst &inst) {
	DebugInstInfo(inst);

	Value *lhs = NULL,
			*rhs = NULL;

	if (Case (inst, 0, &lhs, &rhs))
		HandleICmpInst(inst, lhs, rhs);
	else
		InterruptionHandler::Do(new MatchingFailure(inst));
}

void PatternMatcher::visitAllocaInst (const AllocaInst &inst)
{
	DebugInstInfo(inst);

	Value *allocated = NULL;
	if (Case (inst, 0, &allocated))
		HandleAllocaInst(inst, allocated);
	else
		InterruptionHandler::Do(new MatchingFailure(inst));
}

void PatternMatcher::visitLoadInst (const LoadInst &inst)
{
	DebugInstInfo(inst);

	Value *ptr= NULL;
	if (Case (inst, 0, &ptr))
		HandleLoadInst(inst, ptr);
	else
		InterruptionHandler::Do(new MatchingFailure(inst));
}

void PatternMatcher::visitStoreInst (const StoreInst &inst)
{
	DebugInstInfo(inst);

	Value *val = NULL;
	Instruction *instruction= NULL;
	Constant *constant = NULL;
	Value *ptr = NULL;
	if (Case (inst, 0, &instruction, &ptr))
		HandleStoreInst(inst, instruction, ptr);
	else if (Case (inst, 0, &constant, &ptr))
		HandleStoreInst(inst, constant, ptr);
	else if (Case (inst, 0, &val, &ptr))
		HandleStoreInst(inst, val, ptr);
	else
		InterruptionHandler::Do(new MatchingFailure(inst));
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














