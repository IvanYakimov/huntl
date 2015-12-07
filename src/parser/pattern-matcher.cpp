#include "pattern-matcher.hpp"
using namespace llvm;

/*
author: Ivan Yakimov
date: 2015
e-mail: ivan.yakimov.research@yandex.ru
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

// --------------------------------------------------------
// Instruction visitors

void PatternMatcher::visitReturnInst (const ReturnInst &inst)
{
	Value *value = NULL;
	if (Case (inst, 0, &value)) {
		//TODO:
	}
	else if (Case (inst, 0)) {
		//TODO:
	}
	else
		/* TODO: */;
}

void PatternMatcher::visitBranchInst(const BranchInst &inst) {
	//TODO:
}

void PatternMatcher::visitICmpInst(const ICmpInst &inst) {
	//TODO:
}

void PatternMatcher::visitAllocaInst (const AllocaInst &inst)
{
	if (inst.getName() == "")
		AddRegister(&inst);

	// always allocates constant_int
	ConstantInt *constant_int = NULL;
	if (Case (inst, 0, &constant_int)) {
		//TODO:
	}
	else
		/*TODO:*/;
}

void PatternMatcher::visitLoadInst (const LoadInst &inst)
{
	if (inst.getName() == "")
			AddRegister(&inst);
	AllocaInst *alloca = NULL;
	if (Case (inst, 0, &alloca)) {
		/*TODO:*/;
	}
	else
		/*TODO:*/;
}

void PatternMatcher::visitStoreInst (const StoreInst &inst)
{
  Value *val = NULL;
  AllocaInst *alloca = NULL;
  if (Case (inst, 0, &val, &alloca)) {
  	  //TODO:
  }
  else // pattern matching fault
	  /*TODO:*/;
}







