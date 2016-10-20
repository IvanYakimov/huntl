#include "transform.hpp"

#include "case.hpp"

namespace transform {
	using namespace llvm;

	std::string Transform::Name(const char* prefix) {
		return std::string(prefix);
	}

	std::string Transform::Name_TY(const char* prefix, llvm::Type* ty) {
		assert (ty->isIntegerTy());
		auto width = ty->getIntegerBitWidth();
		return std::string(prefix) + "_i" + std::to_string(width);
	}

	std::string Transform::Name_PTR(const char* prefix) {
		return std::string(prefix) + "_ptr";
	}

	std::string Transform::Name_VOID(const char* prefix) {
		return std::string(prefix) + "_void";
	}

	llvm::Value* Transform::FirstOp(llvm::Instruction& target) {
		return target.getOperand(0);
	}

	llvm::Value* Transform::SecondOp(llvm::Instruction& target) {
		return target.getOperand(1);
	}

	void Transform::DeclareFunction(std::string name, FunctionType* ftype) {
		Function* f = Function::Create(ftype, Function::ExternalLinkage, name.c_str(), &module_);
		func_table_.emplace(name, f);
	}

	void Transform::DeclareBinOp(Type* ty) {
		assert (ty->isIntegerTy());
		auto opcode = i32;
		auto flag = i16;
		FunctionHeader(voidty, Name_TY(BINOP, ty), {refty, opcode, flag, refty, ty, refty, ty});
	}

	void Transform::DeclareICmp(llvm::IntegerType* ty) {
		assert (ty->isIntegerTy());
		auto cond = i32;
		FunctionHeader(voidty, Name_TY(ICMP, ty), {refty, cond, refty, ty, refty, ty});
	}

	void Transform::DeclareAlloca(llvm::Type* ty) {
		assert (ty->isIntegerTy());
		FunctionHeader(voidty, Name_TY(ALLOCA, ty), {refty, ty});
	}

	void Transform::DeclareLoad() {
		FunctionHeader(voidty, Name(LOAD), {refty, refty});
	}

	void Transform::FunctionHeader(Type* ret, std::string name, std::vector<llvm::Type*> fargs) {
		FunctionType* ftype = FunctionType::get(ret, fargs, false);
		DeclareFunction(name, ftype);
	}

	void Transform::DeclareStore(Type* ty) {
		assert (ty->isIntegerTy());
		FunctionHeader(voidty, Name_TY(STORE, ty), {refty, ty, refty});
	}

	void Transform::DeclareStorePtr() {
		FunctionHeader(voidty, Name_PTR(STORE), {refty, refty});
	}

	void Transform::DeclareITE() {
		FunctionHeader(i1, Name(ITE), {refty, i1});
	}

	void Transform::DeclareRet(Type* ty) {
		FunctionHeader(voidty, Name_TY(RET, ty), {refty, refty, ty});
	}

	void Transform::DeclareRetVoid() {
		FunctionHeader(voidty, Name_VOID(RET), {refty});
	}

	void Transform::InitTypes() {
		LLVMContext& context = module_.getContext();
		voidty = Type::getVoidTy(context);
		stringty = Type::getInt8PtrTy(context);
		i1 = Type::getInt1Ty(context);
		i8 = Type::getInt8Ty(context);
		i16 = Type::getInt16Ty(context);
		i32 = Type::getInt32Ty(context);
		i64 = Type::getInt64Ty(context);
		refty = Type::getInt64Ty(context);
		ptrty = Type::getInt64Ty(context);
	}

	Transform::Transform(Module& module) : module_(module) {
		InitTypes();
		// Declarations:
		// BinaryOperator
		DeclareBinOp(i8); 	DeclareBinOp(i16); 	DeclareBinOp(i32);	DeclareBinOp(i64);
		// ICmp
		DeclareICmp(i8);	DeclareICmp(i16);	DeclareICmp(i32);	DeclareICmp(i64);
		// Alloca
		DeclareAlloca(i8);	DeclareAlloca(i16);	DeclareAlloca(i32);	DeclareAlloca(i64);
		// Load
		DeclareLoad();
		// Store
		DeclareStore(i8);	DeclareStore(i16); 	DeclareStore(i32);	DeclareStore(i64);
		DeclareStorePtr();
		// Branch
		DeclareITE();
		// Ret
		DeclareRet(i8);		DeclareRet(i16);	DeclareRet(i32);	DeclareRet(i64);
		DeclareRetVoid();
	}

	Transform::~Transform() {
	}

	Constant* Transform::BindVal(Value* val) {
		Constant* res = ConstantInt::get(i64, inst_num_++, kNotsigned);
		assert (name_map_.find(val) == name_map_.end());
		name_map_.emplace(val, res);
		return res;
	}

	Constant* Transform::BinOpFlag(llvm::BinaryOperator* binop) {
#warning "dummy for binop flags"
		uint16_t flagvalue = 0;
		if (binop->hasNoInfs()) flagvalue = 1;
		else if (binop->hasNoNaNs()) flagvalue = 2;
		else if (binop->hasNoSignedWrap()) flagvalue = 3;
		else if (binop->hasNoSignedZeros()) flagvalue = 4;
		else if (binop->hasNoUnsignedWrap()) flagvalue = 5;
		return ConstantInt::get(i16, flagvalue, kNotsigned);
	}

	Constant* Transform::OpCode(unsigned int opcode) {
		return ConstantInt::get(i32, opcode, kNotsigned);
	}

	llvm::Constant* Transform::Cond(llvm::ICmpInst::Predicate cond) {
		return ConstantInt::get(i32, (unsigned)cond, kNotsigned);
	}

	// this is a common template
	Constant* Transform::ValId(Value* val) {
		if (isa<Constant>(val))
			return ConstantInt::get(refty, not_ref_, kNotsigned);

		auto it = name_map_.find(val);
#warning "the code below is dummy:"
		if (it == name_map_.end())
			return ConstantInt::get(i64, 999, kNotsigned);
		else
			return it->second;
	}

	Function* Transform::GetFunc(std::string name) {
		auto it = func_table_.find(name);
		assert (it != func_table_.end());
		return it->second;
	}

	Value* Transform::InstrumentTheInst(llvm::Instruction* target, llvm::Function* f, std::vector<llvm::Value*> &fargs) {
		IRBuilder<> builder(target);
		return builder.CreateCall(f, fargs);
	}

	void Transform::visitReturnInst(llvm::ReturnInst &ret) {
		Value *ret_val = NULL;
		if (Case (ret, &ret_val)) {
			auto ty = ret_val->getType();
			if (ty->isIntegerTy()) {
				auto func = GetFunc(Name_TY(RET, ty));
				FuncOps fargs = {BindVal(&ret), ValId(ret_val), ret_val};
				InstrumentTheInst(&ret, func, fargs);
			} else if (ty->isPointerTy()) {
				assert (not "implemented");
			}
		} else if (Case (ret)) {

		} else
			assert(not "implemented");
	}

	void Transform::visitBranchInst(llvm::BranchInst &branch) {
		BasicBlock *iftrue = nullptr,
				*iffalse = nullptr,
				*jump = nullptr;
		Value *cond = nullptr;

		//NOTE: operands are stored in the reversed order! So the pattern does.
		//see: http://llvm.org/docs/doxygen/html/classllvm_1_1BranchInst.html
		if (Case (branch, &cond, &iffalse, &iftrue)) {
			auto func = GetFunc(Name(ITE));
			FuncOps fargs = {ValId(cond), cond};
			auto call = InstrumentTheInst(&branch, func, fargs);
			branch.replaceUsesOfWith(cond, call);
		} else if (Case (branch, &jump)) {
			// do nothing
		} else
			assert (false);
	}

	void Transform::visitBinaryOperator(BinaryOperator &binop) {
		Value *lhs = nullptr, *rhs = nullptr;
		if (Case(binop, &lhs, &rhs)) {
			auto func = GetFunc(Name_TY(BINOP, binop.getType()));
			FuncOps fargs = {BindVal(&binop), OpCode(binop.getOpcode()), BinOpFlag(&binop), ValId(lhs), lhs, ValId(rhs), rhs};
			InstrumentTheInst(&binop, func, fargs);
		} else
			assert (false && "not implemented");
	}

	void Transform::visitICmpInst (llvm::ICmpInst &icmp) {
		Value *lhs = nullptr, *rhs = nullptr;
		if (Case (icmp, &lhs, &rhs)) {
			auto func = GetFunc(Name_TY(ICMP, lhs->getType()));
			FuncOps fargs = {BindVal(&icmp), Cond(icmp.getPredicate()), ValId(lhs), lhs, ValId(rhs), rhs};
			InstrumentTheInst(&icmp, func, fargs);
		} else
			assert (not "implemented");
	}

	void Transform::visitAllocaInst (llvm::AllocaInst &alloca) {
		ConstantInt *const_allocator = nullptr;
		Value *ref_allocator = nullptr;
		Type *allocated_type =  alloca.getAllocatedType();
		auto align = alloca.getAlignment();
		assert (allocated_type->isIntegerTy() and "sorry, only integer allocation supported yet");
		if (Case (alloca, &const_allocator)) {
			auto func = GetFunc(Name_TY(ALLOCA, allocated_type));
			FuncOps fargs = {BindVal(&alloca), const_allocator};
			InstrumentTheInst(&alloca, func, fargs);
		} else if (Case (alloca, &ref_allocator)) {

		} else
			assert (false && "not implemented");
	}

	void Transform::visitLoadInst (llvm::LoadInst &load) {
		Instruction *inst = NULL;
		if (Case (load, &inst)) {
			FuncOps fargs = {BindVal(&load), ValId(inst)};
			InstrumentTheInst(&load, GetFunc(Name(LOAD)), fargs);
		} else
			assert(false);
	}

	void Transform::visitStoreInst (llvm::StoreInst &store) {
		assert (store.getNumOperands() == 2);
		auto src = FirstOp(store), dst = SecondOp(store);
		auto srcty = src->getType();
		if (srcty->isIntegerTy()) {
			auto func = GetFunc(Name_TY(STORE, src->getType()));
			FuncOps fargs = {ValId(src), src, ValId(dst)};
			InstrumentTheInst(&store, func, fargs);
		} else if (srcty->isPointerTy()){
			auto func = GetFunc(Name_PTR(STORE));
			FuncOps fargs = {ValId(src), ValId(dst)};
			InstrumentTheInst(&store, func, fargs);
		} else
			assert (not "implemented");
	}

	void Transform::visitCallInst(llvm::CallInst &call_inst) {

	}
}












