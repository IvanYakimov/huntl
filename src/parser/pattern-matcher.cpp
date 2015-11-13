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

// --------------------------------------------------------
// Instruction visitors

void PatternMatcher::visitAllocaInst (const AllocaInst &inst)
{
	if (inst.getName() == "")
		AddRegister(&inst);

	ConstantInt *constant_int = NULL;
	if (Case (inst, 0, &constant_int)) {
		//TODO:
	}
	else
		;
}

void PatternMatcher::visitLoadInst (const LoadInst &inst)
{
	if (inst.getName() == "")
			AddRegister(&inst);
	AllocaInst *alloca = NULL;
	BinaryOperator *bin_op = NULL;
	if (Case (inst, 0, &alloca)) {
		errs() << "load alloca\n";
	}
	else
		errs() << "load pattern matching failed\n";
}

void PatternMatcher::visitStoreInst (const StoreInst &inst)
{
  ConstantInt *constant_int = NULL;
  ConstantFP *constant_fp = NULL;
  Argument *arg = NULL;
  AllocaInst *alloca = NULL;
  BinaryOperator *bin_op = NULL;
  if (Case (inst, 0, &arg, &alloca)) {
  	  errs() << "store argument, alloca\n";
  }
  else if (Case (inst, 0, &bin_op, &alloca)) {
	  errs() << "store bin_op, alloca\n";
  }
  else if (Case (inst, 0, &constant_int, &alloca)) {
	  errs() << "store constant_int, alloca\n";
  }
  else if (Case (inst, 0, &constant_fp, &alloca)) {
	  errs() << "store constant_fp, alloca\n";
  }
  else // pattern matching fault
	  errs() << "store pattern matching failed\n";
}

void PatternMatcher::visitReturnInst (const ReturnInst &inst)
{
	Value *value = NULL;
	ConstantInt *constant_int = NULL;
	BinaryOperator *bin_op = NULL;
	if (Case (inst, 0, &constant_int)) {
		errs() << "ret constant_fp\n";
	}
	else if (Case (inst, 0, &bin_op)) {
		//TODO:
	}
	else if (Case (inst, 0)) {
		errs() << "ret void\n";
	}
	else
		errs() << "ret pattern matching failed\n";
}









