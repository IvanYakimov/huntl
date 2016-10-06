#ifndef __TRANSFORM_HPP__
#define __TRANSFORM_HPP__

# include "llvm/IR/InstVisitor.h"
# include "llvm/IR/Instruction.h"
#include "llvm/IR/Module.h"
# include "llvm/Support/raw_ostream.h"
# include "llvm/Support/Debug.h"
#include "llvm/IR/IRBuilder.h"

namespace transform {
	class Transform : public llvm::InstVisitor <Transform>
	{
	private:
		using Counter = uint64_t;
		Counter inst_num_ = 0;
		llvm::Module& module_;
		std::map <std::string, llvm::Function*> func_table_;

		const char* BINOP_I32 = "binop_i32";

		llvm::Function* GetFunction(std::string name);
		void DeclareFunction(std::string name, llvm::FunctionType* ftype);
		void InitBinOp();
		void InitTypes();
		void InitGlobals();

		llvm::Type* i1;
		llvm::Type* i8;
		llvm::Type* i32;
		llvm::Type* i16;
		llvm::Type* i64;

		llvm::GlobalVariable* status_;
		llvm::GlobalVariable* status_ptr_;
		llvm::Constant* CountNewInst();
		llvm::Constant* GetOpCode(unsigned int opcode);
		const bool kNotsigned = false;
	public:
		Transform(llvm::Module& module);
		~Transform();
		// Specific Instruction type classes
		void visitReturnInst(const llvm::ReturnInst &return_inst);
		void visitBranchInst(const llvm::BranchInst &branch_inst);
		//void visitSwitchInst(const llvm::SwitchInst &switch_inst);
		void visitBinaryOperator(llvm::BinaryOperator &binop);
		void visitICmpInst (const llvm::ICmpInst &icmp_inst);
		// missed instructions
		void visitAllocaInst (const llvm::AllocaInst &alloca_inst);
		void visitLoadInst (const llvm::LoadInst &load_inst);
		void visitStoreInst (const llvm::StoreInst &store_inst);
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
		void visitCallInst(const llvm::CallInst &call_inst);
	};
}

#endif
