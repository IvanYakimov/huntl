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
		errs() << "s\n";
	# endif
	}

	// --------------------------------------------------------
	// Instruction visitors

	void Matcher::visitReturnInst (const ReturnInst &inst) {
		DebugInstInfo(inst);

		Value *ret_val = NULL;
		Instruction *ret_inst = NULL;
		Constant *ret_const = NULL;

		if (Case (inst, &ret_inst))
			HandleReturnInst(inst, ret_inst);
		else if (Case (inst, &ret_const))
			HandleReturnInst(inst, ret_const);
		else if (Case (inst))
			HandleReturnInst(inst);
		else
			assert(false);
	}

	void Matcher::visitBranchInst(const BranchInst &inst) {
		DebugInstInfo(inst);

		BasicBlock *iftrue = NULL,
				*iffalse = NULL,
				*jump = NULL;
		Value *cond = NULL;

		if (Case (inst, &cond, &iftrue, &iffalse))
			HandleBranchInst(inst, cond, iftrue, iffalse);
		else if (Case (inst, &jump))
			HandleBranchInst(inst, jump);
		else
			assert(false);
	}

	void Matcher::visitBinaryOperator(const llvm::BinaryOperator &inst) {
		DebugInstInfo(inst);

		Value *lhs = NULL,
				*rhs = NULL;
		ConstantInt *constant_int = NULL,
				*c2 = NULL;

		if (Case (inst, &constant_int, &rhs)) {
			HandleBinOp(inst, constant_int, rhs);
		}
		else if (Case (inst, &lhs, &constant_int)) {
			HandleBinOp(inst, lhs, constant_int);
		}
		else if (Case (inst, &constant_int, &c2)) {
			assert(false && "not implemented");
		}
		else if (Case (inst, &lhs, &rhs)) {
			HandleBinOp(inst, lhs, rhs);
		}
		else
			assert(false);
	}

	void Matcher::visitICmpInst(const ICmpInst &inst) {
		DebugInstInfo(inst);

		Value *lhs = NULL,
				*rhs = NULL;

		if (Case (inst, &lhs, &rhs))
			HandleICmpInst(inst, lhs, rhs);
		else
			assert(false);
	}

	void Matcher::visitAllocaInst (const AllocaInst &inst)
	{
		DebugInstInfo(inst);

		Value *allocated = NULL;
		ConstantInt *constant_int = NULL;
		if (Case (inst, &constant_int))
			HandleAllocaInst(inst, constant_int);
		else
			assert(false && "not implemented");
	}

	void Matcher::visitLoadInst (const LoadInst &inst)
	{
		DebugInstInfo(inst);

		Instruction *instruction = NULL;
		if (Case (inst, &instruction))
			HandleLoadInst(inst, instruction);
		else
			assert(false);
	}

	void Matcher::visitStoreInst (const StoreInst &inst)
	{
		DebugInstInfo(inst);

		Value *val = NULL;
		Instruction *instruction= NULL;
		ConstantInt *constant_int = NULL;
		Value *ptr = NULL;
		Argument *arg = NULL;

		if (Case (inst, &constant_int, &ptr))
			HandleStoreInst(inst, constant_int, ptr);
		else if (Case (inst, &instruction, &ptr))
			HandleStoreInst(inst, instruction, ptr);
		else if (Case (inst, &arg, &ptr))
			HandleStoreInst(inst, arg, ptr);
		else
			assert(false);
	}

	void Matcher::visitCallInst(const llvm::CallInst &inst) {

	}

	//--------------------
	// Case matcher
	template <typename... Targs>
	bool Matcher::Case(const Instruction &inst, Targs... Fargs) {
		return CaseHelper::Do(inst, 0, Fargs...);
	}

	bool Matcher::CaseHelper::Do (const Instruction &inst, unsigned i)
	{
		if (inst.getNumOperands() != i)
			return false;
		else
			return true;
	}

	template <typename T, typename... Targs>
	bool Matcher::CaseHelper::Do (const Instruction &inst, unsigned i, T value, Targs... Fargs)
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
				return true && Do(inst, ++i, Fargs...);
			}
			else
				return false;
		}
		else
			return false;
	}
}













