#include "case.hpp"

bool Do (const llvm::Instruction &inst, unsigned i)
{
	if (inst.getNumOperands() != i)
		return false;
	else
		return true;
}
