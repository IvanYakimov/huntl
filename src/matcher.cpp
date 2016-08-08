#include "matcher.hpp"
using namespace llvm;

/*
author: Ivan Yakimov
date: 2015
e-mail: ivan.yakimov.research@yandex.ru
*/

namespace interpreter {
	// --------------------------------------------------------
	// Instruction visitors

	void Matcher::visitReturnInst (const ReturnInst &inst) {
		Value *ret_val = NULL;

		if (Case (inst, &ret_val))
			HandleReturnInst(inst, ret_val);
		else if (Case (inst))
			HandleReturnInst(inst);
		else
			assert(false);
	}

	void Matcher::visitBranchInst(const BranchInst &inst) {
		BasicBlock *iftrue = NULL,
				*iffalse = NULL,
				*jump = NULL;
		Value *cond = NULL;

		//NOTE: the operands are stored in reversed order, as follow: (IfTrue, IfFalse, Cond)^R = (Cond, IfFalse, IfTrue)
		//see: http://llvm.org/docs/doxygen/html/classllvm_1_1BranchInst.html
		if (Case (inst, &cond, &iffalse, &iftrue))
			HandleBranchInst(inst, cond, iftrue, iffalse);
		else if (Case (inst, &jump))
			HandleBranchInst(inst, jump);
		else
			assert(false);
	}

	void Matcher::visitBinaryOperator(const llvm::BinaryOperator &inst) {
		Value *lhs = NULL,
				*rhs = NULL;

		if (Case (inst, &lhs, &rhs)) {
			HandleBinOp(inst, lhs, rhs);
		}
		else
			assert(false);
	}

	void Matcher::visitICmpInst(const ICmpInst &inst) {
		Value *lhs = NULL,
				*rhs = NULL;

		if (Case (inst, &lhs, &rhs))
			HandleICmpInst(inst, lhs, rhs);
		else
			assert(false and "unexpected behavior");
	}

	void Matcher::visitAllocaInst (const AllocaInst &inst) {
		//auto op = inst.getOperand(0);
		//std::cerr << utils::Printer::Do(op) << std::endl;
		//llvm::errs() << *inst.getType() << "\n";
		//llvm::errs() << inst << "\n";
		ConstantInt *constant_int = NULL;
		Type *allocated_type = inst.getAllocatedType();
		if (Case (inst, &constant_int))
			HandleAllocaInst(inst, constant_int, allocated_type);
		else
			assert(false && "not implemented");
	}

	void Matcher::visitLoadInst (const LoadInst &inst) {
		Instruction *instruction = NULL;
		if (Case (inst, &instruction))
			HandleLoadInst(inst, instruction);
		else
			assert(false);
	}

	void Matcher::visitGetElementPtrInst (const llvm::GetElementPtrInst &inst) {
		assert (false and "not implemented");
	}

	void Matcher::visitTruncInst (const llvm::TruncInst &inst) {
		Value *value = NULL;
		/*Type *ty = inst.getDestTy();
		assert (ty->isIntegerTy());
		IntegerType *dest_ty = llvm::dyn_cast<IntegerType>(ty);*/
		IntegerType *dest_ty = ExtractDestType<IntegerType, TruncInst>(inst);//llvm::dyn_cast<IntegerType>(ty);
		if (Case (inst, &value))
			HandleTruncInst(inst, value, dest_ty);
		else
			assert (false and "not implemented");
	}

	void Matcher::visitZExtInst (const llvm::ZExtInst &inst) {
		Value *value = NULL;
		IntegerType *dest_ty = ExtractDestType<IntegerType, ZExtInst>(inst);
		if (Case (inst, &value))
			HandleZExtInst (inst, value, dest_ty);
		else
			assert (false and "not implemented");
	}

	void Matcher::visitSExtInst (const llvm::SExtInst &inst) {
		Value *value = NULL;
		IntegerType *dest_ty = ExtractDestType<IntegerType, SExtInst>(inst);
		if (Case (inst, &value))
			HandleSExtInst (inst, value, dest_ty);
		else
			assert (false and "not implemented");
	}

	void Matcher::visitPtrToIntInst (const llvm::PtrToIntInst &inst) {
		Value *value = NULL;
		IntegerType *dest_ty = ExtractDestType<IntegerType, PtrToIntInst>(inst);
		if (Case (inst, &value))
			HandlePtrToInt(inst, value, dest_ty);
		else
			assert (false and "not implemented");
	}

	void Matcher::visitIntToPtrInst (const llvm::IntToPtrInst &inst) {
		Value *value = NULL;
		PointerType *dest_ty = ExtractDestType<PointerType, IntToPtrInst>(inst);
		if (Case (inst, &value))
			HandleIntToPtr(inst, value, dest_ty);
		else
			assert (false and "not implemented");
	}

	void Matcher::visitBitCastInst (const llvm::BitCastInst &inst) {
		assert (false and "not implemented");
	}

	void Matcher::visitStoreInst (const StoreInst &inst)
	{
		Value *val = NULL;
		Value *ptr = NULL;

		if (Case (inst, &val, &ptr))
			HandleStoreInst(inst, val, ptr);
		else
			assert(false);
	}

	void Matcher::visitCallInst(const llvm::CallInst &inst) {
		HandleCallInst(inst);
	}

	//--------------------
	// Case matcher
	template <class D, class I>
	D* Matcher::ExtractDestType(const I &inst) {
		Type *ty = inst.getDestTy();
		//assert (ty->isIntegerTy());
		D* res = llvm::dyn_cast<D>(ty);
		assert (res != nullptr);
		return res;
	}

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













