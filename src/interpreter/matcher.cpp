#include "matcher.hpp"
using namespace llvm;

/*
author: Ivan Yakimov
date: 2015
e-mail: ivan.yakimov.research@yandex.ru
*/

namespace interpreter {
	void Matcher::DebugInstInfo(const llvm::Instruction &inst) {
	# ifdef DBG
		errs() << inst << "\n";
	# endif
	}

	void Matcher::DebugOpList(const llvm::Instruction &inst) {
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

	void Matcher::visitReturnInst (const ReturnInst &inst) {
		DebugInstInfo(inst);

		Value *ret_val = NULL;
		Instruction *ret_inst = NULL;
		Constant *ret_const = NULL;

		if (Case (inst, 0, &ret_inst))
			HandleReturnInst(inst, ret_inst);
		else if (Case (inst, 0, &ret_const))
			HandleReturnInst(inst, ret_const);
		else if (Case (inst, 0, &ret_val))
			HandleReturnInst(inst, ret_val);
		else if (Case (inst, 0))
			HandleReturnInst(inst);
		else
			; // Matching failure
	}

	void Matcher::visitBranchInst(const BranchInst &inst) {
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
			; // Matching failure
	}

	void Matcher::visitICmpInst(const ICmpInst &inst) {
		DebugInstInfo(inst);

		Value *lhs = NULL,
				*rhs = NULL;

		if (Case (inst, 0, &lhs, &rhs))
			HandleICmpInst(inst, lhs, rhs);
		else
			; // Matching Failure
	}

	void Matcher::visitAllocaInst (const AllocaInst &inst)
	{
		DebugInstInfo(inst);

		Value *allocated = NULL;
		if (Case (inst, 0, &allocated))
			HandleAllocaInst(inst, allocated);
		else
			; // Matching Failure
	}

	void Matcher::visitLoadInst (const LoadInst &inst)
	{
		DebugInstInfo(inst);

		Value *ptr= NULL;
		if (Case (inst, 0, &ptr))
			HandleLoadInst(inst, ptr);
		else
			; // Matching Failure
	}

	void Matcher::visitStoreInst (const StoreInst &inst)
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
			; // Matching Failure
	}

	//--------------------
	// Helper methods
	bool Matcher::Case (const Instruction &inst, unsigned i)
	{
		if (inst.getNumOperands() != i)
			return false;
		else
			return true;
	}

	template <typename T, typename... Targs>
	bool Matcher::Case (const Instruction &inst, unsigned i, T value, Targs... Fargs)
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
}













