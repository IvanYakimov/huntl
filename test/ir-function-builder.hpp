#ifndef __IR_FUNCTION_BUILDER_HPP__
#define __IR_FUNCTION_BUILDER_HPP__

#include "llvm/IR/Verifier.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Module.h"
# include "llvm/Support/raw_ostream.h"

#include "../src/holder.hpp"
#include "../src/creatable.hpp"

#include <tuple>
#include "../src/activation.hpp"
#include "../src/context.hpp"

using namespace llvm;

class Func {
public:
	Func(Function* func);
	Func(FunctionType* ty, const char* name);
	virtual ~Func();
	Function* Get();
	BasicBlock* Entry();
	BasicBlock* Block(const char* name);
	void Enter(BasicBlock* block);
	AllocaInst* Alloca8(const char *name);
	AllocaInst* Alloca16(const char *name);
	AllocaInst* Alloca32(const char *name);
	AllocaInst* Alloca64(const char *name);
	ConstantInt* I8(uint8_t val);
	ConstantInt* I16(uint16_t val);
	ConstantInt* I32(uint32_t val);
	ConstantInt* I64(uint64_t val);
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
	CallInst* Call(Value* f, Value *arg);
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

struct IntArg;

using IntArgPtr = std::shared_ptr<IntArg>;

struct IntArg {
	unsigned width_;
	std::string name_;
	memory::HolderPtr holder_;
	llvm::Value* address_;
	IntArg(unsigned width, std::string name, memory::HolderPtr holder, llvm::Value* address);
	static std::shared_ptr<IntArg> Create(unsigned width, std::string name, memory::HolderPtr holder, llvm::Value* address);
};

llvm::Function* MkSymI32(llvm::Module* module);

llvm::Function* MkIntFunc(llvm::Module* module, const char* name, std::vector<std::tuple<unsigned, const char*>> int_args, unsigned ret_size = 0);

class Int32Func : public Func {
public:
	Int32Func(const char* name = "f");
};

class VoidFunc : public Func {
public:
	VoidFunc(const char* name = "f");
};

#endif /* __IR_FUNCTION_BUILDER_HPP__ */













