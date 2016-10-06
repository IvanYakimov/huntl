# ifndef __MATCHER_HPP__
# define __MATCHER_HPP__

/* 
author: Ivan Yakimov
date: 2015
e-mail: ivan.yakimov.research@yandex.ru
*/

// useful links:
/*
http://en.cppreference.com/w/cpp/language/parameter_pack
http://www.cplusplus.com/reference/type_traits/remove_pointer/
 */

# include "llvm/IR/InstVisitor.h"
# include "llvm/IR/Instruction.h"
#include "llvm/IR/Module.h"
# include "llvm/Support/raw_ostream.h"
# include "llvm/Support/Debug.h"

#include "printer.hpp"
#include "case.hpp"

# include <type_traits>
# include <map>
# include <string>
# include <memory>
# include <exception>
# include <ostream>
#include <iostream>

namespace interpreter {
	//TODO: refactoring
	//TODO: handling of unsupporter instructions!

	class Matcher : public llvm::InstVisitor <Matcher>
	{
	public:
		Matcher () {}
		virtual ~Matcher () {}

		// Specific Instruction type classes
		void visitReturnInst(const llvm::ReturnInst &return_inst);
		void visitBranchInst(const llvm::BranchInst &branch_inst);
		void visitSwitchInst(const llvm::SwitchInst &switch_inst);
		// missed instructions
		void visitBinaryOperator(const llvm::BinaryOperator &binary_operator);
		void visitICmpInst (const llvm::ICmpInst &icmp_inst);
		// missed instructions
		void visitAllocaInst (const llvm::AllocaInst &alloca_inst);
		void visitLoadInst (const llvm::LoadInst &load_inst);
		void visitStoreInst (const llvm::StoreInst &store_inst);
		// missed
		void visitGetElementPtrInst (const llvm::GetElementPtrInst &getelementptr_inst);
		void visitPHINode(const llvm::PHINode &phi_node);
		void visitTruncInst (const llvm::TruncInst &trunc_inst);
		void visitZExtInst (const llvm::ZExtInst &zext_inst);
		void visitSExtInst (const llvm::SExtInst &sext_inst);
		// missed
		void visitPtrToIntInst (const llvm::PtrToIntInst &ptrtoint_inst);
		void visitIntToPtrInst (const llvm::IntToPtrInst &inttoptr_inst);
		void visitBitCastInst (const llvm::BitCastInst &bitcast_inst);
		// missed
		void visitSelectInst(const llvm::SelectInst& select_inst);
		// missed
		void visitCallInst(const llvm::CallInst &call_inst);

	protected:
		// Return
		virtual void HandleReturnInst (const llvm::ReturnInst &inst, const llvm::Value *ret_inst) = 0;
		virtual void HandleReturnInst (const llvm::ReturnInst &inst) = 0;

		// Branch
		virtual void HandleBranchInst (const llvm::BranchInst &inst, const llvm::Value *cond, const llvm::BasicBlock *iftrue, const llvm::BasicBlock *iffalse) = 0;
		virtual void HandleBranchInst (const llvm::BranchInst &inst, const llvm::BasicBlock *jump) = 0;

		// Switch
		virtual void HandleSwitchInst (const llvm::SwitchInst& switch_inst) = 0;

		// BinOp
		virtual void HandleBinOp (const llvm::BinaryOperator &inst, const llvm::Value *lhs, const llvm::Value *rhs) = 0;
		// Cmp
		virtual void HandleICmpInst (const llvm::ICmpInst &inst, const llvm::Value *lhs, const llvm::Value *rhs) = 0;

		// Alloca
		virtual void HandleAllocaInst (const llvm::AllocaInst &inst, const llvm::ConstantInt *allocated, const llvm::Type *allocated_type) = 0;

		// Load
		virtual void HandleLoadInst (const llvm::LoadInst &inst, const llvm::Value *ptr) = 0;
		// Store
		virtual void HandleStoreInst (const llvm::StoreInst &inst, const llvm::Value *target, const llvm::Value *ptr) = 0;
		// GetElementPtr
		virtual void HandleGetElementPtr (const llvm::GetElementPtrInst& inst, const llvm::Value *target, const llvm::Value *start_from, const llvm::Value *index) = 0;
		virtual void HandleGetElementPtr (const llvm::GetElementPtrInst& inst, const llvm::Value *target, const llvm::Value *index) = 0;


		// Trunc
		virtual void HandleTruncInst (const llvm::TruncInst &inst, const llvm::Value* target, const llvm::IntegerType* dest_ty) = 0;
		// ZExt
		virtual void HandleZExtInst (const llvm::ZExtInst &inst, const llvm::Value* target, const llvm::IntegerType* dest_ty) = 0;
		// SExt
		virtual void HandleSExtInst (const llvm::SExtInst &inst, const llvm::Value* target, const llvm::IntegerType* dest_ty) = 0;
		// IntToPtr
		virtual void HandlePtrToInt (const llvm::PtrToIntInst &inst, const llvm::Value* target, const llvm::IntegerType* dest_ty) = 0;
		// PtrToInt
		virtual void HandleIntToPtr (const llvm::IntToPtrInst &inst, const llvm::Value* target, const llvm::PointerType* dest_ty) = 0;

		// Phi
		virtual void HandlePHINode(const llvm::PHINode &phi_node) = 0;

		// Select
		virtual void HandleSelectInst(const llvm::SelectInst &select_inst) = 0;

		// Call
		virtual void HandleCallInst(const llvm::CallInst &inst) = 0;
		/*
	protected:
		template <class D, class I>
		D* ExtractDestType(const I &inst);

		// "pattern matching"
		template <typename... Targs>
		bool Case (const llvm::Instruction &inst, Targs... Fargs); // inductive casen

		class CaseHelper {
		public:
		// "pattern matching"
		protected:
			static bool Do (const llvm::Instruction &inst, unsigned i); // base case
			template <typename T, typename... Targs>
			static bool Do (const llvm::Instruction &inst, unsigned i, T value, Targs... Fargs); // inductive case
			template <typename... Targs> friend bool Matcher::Case (const llvm::Instruction &inst, Targs... Fargs); // inductive casen
		};

		static inline void DebugInstInfo(const llvm::Instruction &inst);
		static inline void DebugOpList(const llvm::Instruction &inst);
		*/
	};
}

# endif /* __INST_PRINTER_HPP__ */








