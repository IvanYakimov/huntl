#include "pattern-matcher.hpp"
using namespace llvm;

bool PatternMatcher::Case (const Instruction &inst, unsigned i)
{
	if (inst.getNumOperands () != i)
		return false;
	else
		return true;
}

template <typename T, typename... Targs>
bool PatternMatcher::Case (const Instruction &inst, unsigned i, T value, Targs... Fargs)
{
	typedef typename std::remove_pointer <T>::type pV;
	typedef typename std::remove_pointer <pV>::type V;
	auto operand = inst.getOperand (i);
	if (isa <V> (operand)) {
		*value = dyn_cast <V> (operand);
		return true && Case (inst, ++i, Fargs...);
	}
	else
		return false;
}

void PatternMatcher::visitAllocaInst (const AllocaInst &inst)
{
  register_map_->Add (&inst);
  //TODO: pattern matching
}

void PatternMatcher::visitLoadInst (const LoadInst &inst)
{
  register_map_->Add (&inst);
  //TODO: pattern matching
}

void PatternMatcher::visitStoreInst (const StoreInst &inst)
{
  ConstantInt *const_int = NULL;
  Argument *arg = NULL;
  AllocaInst *alloca = NULL;
  if (Case (inst, 0, &const_int, &alloca)) {
	  HandleStoreInst (const_int, alloca);
  }
  else if (Case (inst, 0, &arg, &alloca)) {
	  HandleStoreInst (arg, alloca);
  }
  else // pattern matching fault
	  HandleStoreInst (inst);
}











