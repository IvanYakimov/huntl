#include "ir-function-builder.hpp"

Func::Func(Function* func) : context_(getGlobalContext()), builder_(context_), func_(func) {
	entry_ = Block("entry");
	Enter(entry_);
}

//TODO: refactoring - use module context instead of getGlobalContext
Func::Func(FunctionType* ty, const char* name) : builder_(getGlobalContext()), context_(getGlobalContext()) {
	module_ = new Module("test", context_);
	func_= Function::Create(ty, Function::InternalLinkage, name, module_);
	entry_ = Block("entry");
	Enter(entry_);
}

Func::~Func() {
	delete module_;
}

Function* Func::Get() {
	return func_;
}

BasicBlock* Func::Entry() {
	return entry_;
}

BasicBlock* Func::Block(const char* name) {
	return BasicBlock::Create(context_, name, func_);
}

void Func::Enter(BasicBlock* block) {
	builder_.SetInsertPoint(block);
}


AllocaInst* Func::Alloca32(const char *name) {
	AllocaInst* res = builder_.CreateAlloca(Type::getInt32Ty(context_), 0, name);
	res->setAlignment(4);
	return res;
}

ConstantInt* Func::I32(uint32_t val) {
	return ConstantInt::get(context_, APInt(32, val, true));
}

ConstantInt* Func::I1(bool val) {
	if (val == true)
		return ConstantInt::get(context_, APInt(1, 1, true));
	else
		return ConstantInt::get(context_, APInt(1, 0, true));
}

ConstantInt* Func::True() {
	return I1(true);
}

ConstantInt* Func::False() {
	return I1(false);
}

StoreInst* Func::Store(Value* what, Value* where) {
	StoreInst* res = builder_.CreateStore(what, where);
	res->setAlignment(4);
	return res;
}

LoadInst* Func::Load(Value *from) {
	LoadInst* res = builder_.CreateLoad(from);
	res->setAlignment(4);
	return res;
}

ReturnInst* Func::Ret(Value *what) {
	return builder_.CreateRet(what);
}

ReturnInst* Func::RetVoid() {
	return builder_.CreateRetVoid();
}

Value* Func::EQ(Value* lhs, Value* rhs) {
	return builder_.CreateICmpEQ(lhs, rhs);
}

Value* Func::NE(Value* lhs, Value* rhs) {
	return builder_.CreateICmpNE(lhs, rhs);
}

BranchInst* Func::IfThanElse(Value* cond, BasicBlock* iftrue, BasicBlock* iffalse) {
	return builder_.CreateCondBr(cond, iftrue, iffalse);
}

BranchInst* Func::Jump(BasicBlock* dest) {
	return builder_.CreateBr(dest);
}

Value* Func::Add(Value* lhs, Value* rhs) {
	return builder_.CreateAdd(lhs, rhs);
}

//TODO: Make variadic
PHINode* Func::Phi(Type* ty) {
	return builder_.CreatePHI(ty, 0);
}

Value* Func::ZExt(Value* val, Type* ty){
	return builder_.CreateZExt(val, ty);
}

Type* Func::Int32Ty() {
	return Type::getInt32Ty(context_);
}

Type* Func::Int1Ty() {
	return Type::getInt1Ty(context_);
}

Type* Func::VoidTy() {
	return Type::getVoidTy(context_);
}

Int32Func::Int32Func(const char* name) : Func(FunctionType::get(Type::getInt32Ty(getGlobalContext()), false), name) {}
VoidFunc::VoidFunc(const char* name) : Func(FunctionType::get(Type::getVoidTy(getGlobalContext()), false), name) {}

IntArg::IntArg(unsigned width, std::string name, memory::HolderPtr holder, llvm::Value* address) :
		width_(width),
		name_(name),
		holder_(holder),
		address_(address) {

}

std::shared_ptr<IntArg> IntArg::Create(unsigned width, std::string name, memory::HolderPtr holder, llvm::Value* address) {
	return utils::Create<IntArg>(width, name, holder, address);
}

llvm::Function* MkSymI32(llvm::Module* module) {
	llvm::FunctionType* f_type = FunctionType::get(Type::getInt32Ty(getGlobalContext()), false);
	auto raw_func = llvm::Function::Create(f_type, Function::ExternalLinkage, "mksym_i32", module);
	return raw_func;
}

llvm::Function* MkIntFunc(llvm::Module* module, memory::ActivationPtr act, const char* name, std::vector<std::tuple<unsigned, const char*, memory::HolderPtr>> int_args, unsigned ret_size) {
	std::vector<Type*> f_args;
	for (auto i = int_args.begin(); i != int_args.end(); i++) {
		unsigned width = std::get<0>(*i);
		f_args.push_back(IntegerType::get(module->getContext(), width));
	}

	llvm::FunctionType* f_type = llvm::FunctionType::get(
			IntegerType::get(module->getContext(), ret_size),
			f_args,
			false
			);

	auto raw_func = llvm::Function::Create(f_type, Function::InternalLinkage, name, module);
	int index = 0;
	for (auto args_it = raw_func->arg_begin(); args_it != raw_func->arg_end(); args_it++) {
		llvm::Value* arg = args_it;
		arg->setName(std::get<1>(int_args[index]));
		act->SetArg(arg, std::get<2>(int_args[index]));
		index++;
	}
	return raw_func;
}















