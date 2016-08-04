#ifndef __TEST_MATCHER_TPP__
#define __TEST_MATCHER_TPP__

#include "llvm/IR/InstVisitor.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/Instructions.h"
#include <type_traits>

namespace utils {
	using llvm::isa;
	using llvm::dyn_cast;
	using llvm::Instruction;

	//--------------------
	// Case matcher
	template <typename... Targs>
	bool Case(const Instruction &inst, Targs... Fargs) {
		return CaseHelper(inst, 0, Fargs...);
	}

	bool CaseHelper(const Instruction &inst, unsigned i)
	{
		if (inst.getNumOperands() != i)
			return false;
		else
			return true;
	}

	template <typename T, typename... Targs>
	bool CaseHelper(const Instruction &inst, unsigned i, T value, Targs... Fargs)
	{
		typedef typename std::remove_pointer<T>::type pV;
		typedef typename std::remove_pointer<pV>::type V;
		// Does the following operand exist?
		if (i + 1 <= inst.getNumOperands()) {
			auto operand = inst.getOperand (i);
			// Does the i-th operand have an appropriate type?
			if (isa<V>(operand)) {
				*value = dyn_cast<V>(operand);
				// Check the next operand
				return true && CaseHelper(inst, ++i, Fargs...);
			}
			else
				return false;
		}
		else
			return false;
	}
}
	
#endif
