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
		using FormalArgs = std::vector<llvm::Type*>;
		using FuncOps = std::vector<llvm::Value*>;
		using FuncTable = std::map <std::string, llvm::Function*>;
		using IdMap = std::map <llvm::Value*, llvm::Constant*>;

		Counter not_ref_ = 0;
		Counter inst_num_ = 1;
		llvm::Module& module_;
		FuncTable func_table_;
		IdMap name_map_;

		const bool kNotsigned = false;

		const char* BINOP = "binop";
		const char* ICMP = "icmp";
		const char* ALLOCA = "alloca";
		const char* LOAD = "load";
		const char* STORE = "store";
		const char* ITE = "ite";
		const char* JUMP = "jump";
		const char* RET = "ret";

		llvm::Type* voidty;
		llvm::Type* stringty;
		llvm::IntegerType* i1;
		llvm::IntegerType* i8;
		llvm::IntegerType* i32;
		llvm::IntegerType* i16;
		llvm::IntegerType* i64;
		llvm::Type* refty;
		llvm::Type* ptrty;
		void InitTypes();

		void FunctionHeader(llvm::Type* ret, std::string name, std::vector<llvm::Type*> args);
		void DeclareFunction(std::string name, llvm::FunctionType* ftype);

		std::string Name(const char* prefix);
		std::string Name_TY(const char* prefix, llvm::Type* ty);
		std::string Name_PTR(const char* prefix);
		std::string Name_VOID(const char* prefix);
		llvm::Value* FirstOp(llvm::Instruction& target);
		llvm::Value* SecondOp(llvm::Instruction& target);

		void DeclareBinOp(llvm::Type* ty);
		void DeclareICmp(llvm::IntegerType* ty);
		void DeclareAlloca(llvm::Type* ty);
		void DeclareLoad();
		void DeclareStore(llvm::Type* ty);
		void DeclareStorePtr();
		void DeclareITE();
		void DeclareRet(llvm::Type* ty);
		void DeclareRetVoid();

		llvm::Constant* BindVal(llvm::Value* val);
		llvm::Constant* ValId(llvm::Value* val);
		llvm::Constant* OpCode(unsigned int opcode);
		llvm::Constant* Cond(llvm::ICmpInst::Predicate cond);
		llvm::Constant* BinOpFlag(llvm::BinaryOperator* binop);
		llvm::Function* GetFunc(std::string name);

		llvm::Value* InstrumentTheInst(llvm::Instruction* target, llvm::Function* f, std::vector<llvm::Value*> &fargs);

	public:
		Transform(llvm::Module& module);
		~Transform();
		// Specific Instruction type classes
		void visitReturnInst(llvm::ReturnInst &return_inst);
		void visitBranchInst(llvm::BranchInst &branch_inst);
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
