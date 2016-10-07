#ifndef __TRANSFORM_HPP__
#define __TRANSFORM_HPP__

# include "llvm/IR/InstVisitor.h"
# include "llvm/IR/Instruction.h"
#include "llvm/IR/Module.h"
# include "llvm/Support/raw_ostream.h"
# include "llvm/Support/Debug.h"
#include "llvm/IR/IRBuilder.h"

#include <iostream>

namespace transform {
	class Transform : public llvm::InstVisitor <Transform>
	{
	private:
		using Counter = uint64_t;
		Counter inst_num_ = 0;
		llvm::Module& module_;
		std::map <std::string, llvm::Function*> func_table_;
		std::map <llvm::Value*, llvm::Constant*> name_map_;

		const char* BINOP_PREFIX = "binop";
		const char* ICMP_PREFIX = "icmp";
		const char* ALLOCA_PREFIX = "alloca";

		llvm::Function* GetFunction(std::string name);
		void DeclareFunction(std::string name, llvm::FunctionType* ftype);
		void DeclareBinOp(llvm::Type* ty);
		void DeclareICmp(llvm::Type* ty);
		void DeclareAlloca(llvm::Type* ty);
		void InitTypes();

		std::string ProduceFuncName(const char* prefix, llvm::Type* ty);

		llvm::Type* void_;
		llvm::Type* string_;
		llvm::Type* i1;
		llvm::Type* i8;
		llvm::Type* i32;
		llvm::Type* i16;
		llvm::Type* i64;

		llvm::GlobalVariable* status_;
		llvm::GlobalVariable* status_ptr_;
		llvm::Constant* BindValue(llvm::Value* val);
		llvm::Constant* GetValueId(llvm::Value* val);
		llvm::Constant* GetOpCode(unsigned int opcode);
		llvm::Constant* GetCond(llvm::ICmpInst::Predicate cond);
		llvm::Constant* GetBinOpFlag(llvm::BinaryOperator* binop);
		void InstrumentTheInst(llvm::Instruction* target, llvm::Function* f, std::vector<llvm::Value*> &fargs);
		const bool kNotsigned = false;
	public:
		Transform(llvm::Module& module);
		~Transform();
		// Specific Instruction type classes
		void visitReturnInst(const llvm::ReturnInst &return_inst);
		void visitBranchInst(const llvm::BranchInst &branch_inst);
		//void visitSwitchInst(const llvm::SwitchInst &switch_inst);
		void visitBinaryOperator(llvm::BinaryOperator &binop);
		void visitICmpInst (llvm::ICmpInst &icmp);
		// missed instructions
		void visitAllocaInst (llvm::AllocaInst &alloca);
		void visitLoadInst (llvm::LoadInst &load);
		void visitStoreInst (llvm::StoreInst &store);
		// missed
		/*
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
		*/
		// missed
		void visitCallInst(llvm::CallInst &call);
	};
}

#endif
