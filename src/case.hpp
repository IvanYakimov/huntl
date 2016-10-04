#ifndef __CASE_HPP__
#define __CASE_HPP__

# include "llvm/IR/InstVisitor.h"
# include "llvm/IR/Instruction.h"
#include "llvm/IR/Module.h"
# include "llvm/Support/raw_ostream.h"
# include "llvm/Support/Debug.h"

	template <class D, class I>
	D* ExtractDestType(const I &inst) {
		llvm::Type *ty = inst.getDestTy();
		//assert (ty->isIntegerTy());
		D* res = llvm::dyn_cast<D>(ty);
		assert (res != nullptr);
		return res;
	}

	bool Do (const llvm::Instruction &inst, unsigned i)
	{
		if (inst.getNumOperands() != i)
			return false;
		else
			return true;
	}

	template <typename T, typename... Targs>
	bool Do (const llvm::Instruction &inst, unsigned i, T value, Targs... Fargs)
	{
		typedef typename std::remove_pointer<T>::type pV;
		typedef typename std::remove_pointer<pV>::type V;
		// Does the following operand exist?
		if (i + 1 <= inst.getNumOperands()) {
			auto operand = inst.getOperand (i);
			// Does the i-th operand have an appropriate type?
			if (llvm::isa<V>(operand)) {
				*value = llvm::dyn_cast<V>(operand);
				// Check the next operand
				return true && Do(inst, ++i, Fargs...);
			}
			else
				return false;
		}
		else
			return false;
	}

	template <typename... Targs>
	bool Case(const llvm::Instruction &inst, Targs... Fargs) {
		return Do(inst, 0, Fargs...);
	}

#endif
