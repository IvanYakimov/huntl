#ifndef __IR_FUNCTION_BUILDER_HPP__
#define __IR_FUNCTION_BUILDER_HPP__

#include "llvm/IR/Verifier.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Module.h"
# include "llvm/Support/raw_ostream.h"

using namespace llvm;

class Func {
public:
	Func(FunctionType* ty, const char* name);
	virtual ~Func();
	Function* Get();
	BasicBlock* Entry();
	BasicBlock* Block(const char* name);
	void Enter(BasicBlock* block);
	AllocaInst* Alloca32(const char *name);
	ConstantInt* I32(uint32_t val);
	ConstantInt* I1(bool val);
	ConstantInt* True();
	ConstantInt* False();
	StoreInst* Store(Value* what, Value* where);
	LoadInst* Load(Value *from);
	ReturnInst* Ret(Value *what);
	ReturnInst* RetVoid();
	Value* EQ(Value* lhs, Value* rhs);
	Value* NE(Value* lhs, Value* rhs);
	BranchInst* IfThanElse(Value* cond, BasicBlock* iftrue, BasicBlock* iffalse);
	BranchInst* Jump(BasicBlock* dest);
	Value* Add(Value* lhs, Value* rhs);
	//TODO: Make variadic
	PHINode* Phi(Type* ty);
	Value* ZExt(Value* val, Type* ty);
	Type* Int32Ty();
	Type* Int1Ty();
	Type* VoidTy();
protected:
	LLVMContext &context_ ;// = getGlobalContext();
	IRBuilder<> builder_ ;//(getGlobalContext());
	Module* module_ = nullptr;
	FunctionType* func_ty_ = nullptr;
	Function* func_ = nullptr;
	BasicBlock* entry_ = nullptr;
};

class Int32Func : public Func {
public:
	Int32Func(const char* name = "f");
};

class VoidFunc : public Func {
public:
	VoidFunc(const char* name = "f");
};

#endif /* __IR_FUNCTION_BUILDER_HPP__ */
