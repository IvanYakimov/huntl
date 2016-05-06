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

		if (Case (inst, &ret_inst))
			HandleReturnInst(inst, ret_inst);
		else if (Case (inst, &ret_const))
			HandleReturnInst(inst, ret_const);
		else if (Case (inst))
			HandleReturnInst(inst);
		else
			throw Failure(); // Matching failure
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
			throw Failure(); // Matching failure
	}

	void Matcher::visitBinaryOperator(const llvm::BinaryOperator &inst) {
		DebugInstInfo(inst);

		Value *lhs = NULL,
				*rhs = NULL;

		if (Case (inst, &lhs, &rhs)) {
			auto op_code = inst.getOpcode();
			//TODO: check this code
			Assert<Support>(not (op_code == Instruction::FAdd or
					op_code == Instruction::FSub or
					op_code == Instruction::FMul or
					op_code == Instruction::FDiv or
					op_code == Instruction::FRem));
			HandleBinOp(inst, lhs, rhs);
		}
		else
			throw Failure();
	}

	void Matcher::visitICmpInst(const ICmpInst &inst) {
		DebugInstInfo(inst);

		Value *lhs = NULL,
				*rhs = NULL;

		if (Case (inst, &lhs, &rhs))
			HandleICmpInst(inst, lhs, rhs);
		else
			throw Failure(); // Matching Failure
	}

	void Matcher::visitAllocaInst (const AllocaInst &inst)
	{
		DebugInstInfo(inst);

		Value *allocated = NULL;
		if (Case (inst, &allocated))
			HandleAllocaInst(inst, allocated);
		else
			throw Failure(); // Matching Failure
	}

	void Matcher::visitLoadInst (const LoadInst &inst)
	{
		DebugInstInfo(inst);

		Value *ptr= NULL;
		if (Case (inst, &ptr))
			HandleLoadInst(inst, ptr);
		else
			throw Failure(); // Matching Failure
	}

	void Matcher::visitStoreInst (const StoreInst &inst)
	{
		DebugInstInfo(inst);

		Value *val = NULL;
		Instruction *instruction= NULL;
		Constant *constant = NULL;
		Value *ptr = NULL;

		if (Case (inst, &instruction, &ptr))
			HandleStoreInst(inst, instruction, ptr);
		else if (Case (inst, &constant, &ptr))
			HandleStoreInst(inst, constant, ptr);
		else
			throw Failure(); // Matching Failure
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













