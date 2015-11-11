#include "pattern-matcher.hpp"
using namespace llvm;

/*
author: Ivan Yakimov
date: 2015
e-mail: ivan.yakimov.research@yandex.ru
Licensed under LGPL license.
*/

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

void PatternMatcher::visitAllocaInst (const AllocaInst &inst)
{
	if (inst.getName() == "")
		AddRegister(&inst);

	Constant *const_val = NULL;
	if (Case (inst, 0, &const_val)) {
		HandleAllocaInst(inst, const_val);
	}
	else
		HandleAllocaInst(inst);
}

void PatternMatcher::visitLoadInst (const LoadInst &inst)
{
	AddRegister(&inst);
	//TODO: pattern matching
}

void PatternMatcher::visitStoreInst (const StoreInst &inst)
{
  ConstantInt *const_int = NULL;
  Argument *arg = NULL;
  AllocaInst *alloca = NULL;
  if (Case (inst, 0, &const_int, &alloca)) {
	  HandleStoreInst(inst, const_int, alloca);
  }
  else if (Case (inst, 0, &arg, &alloca)) {
	  HandleStoreInst(inst, arg, alloca);
  }
  else // pattern matching fault
	  HandleStoreInst(inst);
}

void PatternMatcher::visitReturnInst (const ReturnInst &inst)
{
	ConstantInt *const_int = NULL;
	Argument *arg = NULL;
	if (Case (inst, 0, &const_int)) {
		HandleReturnInst(inst, const_int);
	}
	else
		HandleReturnInst(inst);
}









