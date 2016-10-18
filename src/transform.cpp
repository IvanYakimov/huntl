#include "transform.hpp"

#include "case.hpp"

namespace transform {
	using namespace llvm;

	std::string Transform::ProduceFuncName(const char* prefix, llvm::Type* ty) {
		assert (ty->isIntegerTy());
		auto width = ty->getIntegerBitWidth();
		return std::string(prefix) + "_i" + std::to_string(width);
	}

	void Transform::DeclareFunction(std::string name, FunctionType* ftype) {
		Function* f = Function::Create(ftype, Function::ExternalLinkage, name.c_str(), &module_);
		func_table_.emplace(name, f);
	}

	void Transform::DeclareBinOp(Type* ty) {
		assert (ty->isIntegerTy());
		auto opcode = i32;
		auto flag = i16;
		std::vector<Type*> fargs = {refty, opcode, flag, refty, ty, refty, ty};
		FunctionType* ftype = FunctionType::get(voidty, fargs, false);
		DeclareFunction(ProduceFuncName(BINOP_PREFIX, ty), ftype);
	}

	void Transform::DeclareICmp(llvm::Type* ty) {
		assert (ty->isIntegerTy());
		auto cond = i32;
		std::vector<Type*> fargs = {refty, cond, refty, ty, refty, ty};
		FunctionType* ftype = FunctionType::get(voidty , fargs, false);
		DeclareFunction(ProduceFuncName(ICMP_PREFIX, ty), ftype);
	}

	void Transform::DeclareAlloca(llvm::Type* ty) {
		assert (ty->isIntegerTy());
		std::vector<Type*> fargs = {refty, ty};
		FunctionType* ftype = FunctionType::get(voidty, fargs, false /*isn't VarArg*/);
		DeclareFunction(ProduceFuncName(ALLOCA_PREFIX, ty), ftype);
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
	}

	Transform::~Transform() {
	}

	Constant* Transform::BindValue(Value* val) {
		Constant* res = ConstantInt::get(i64, inst_num_++, kNotsigned);
		assert (name_map_.find(val) == name_map_.end());
		name_map_.emplace(val, res);
		return res;
	}

	Constant* Transform::GetOpCode(unsigned int opcode) {
		return ConstantInt::get(i32, opcode, kNotsigned);
	}

	llvm::Constant* Transform::GetCond(llvm::ICmpInst::Predicate cond) {
		return ConstantInt::get(i32, (unsigned)cond, kNotsigned);
	}

	// this is a common template
	Constant* Transform::GetValueId(Value* val) {
		if (isa<Constant>(val))
			return ConstantInt::get(refty, not_ref_, kNotsigned);

		auto it = name_map_.find(val);
#warning "the code below is dummy:"
		if (it == name_map_.end())
			return ConstantInt::get(i64, 999, kNotsigned);
		else
			return it->second;
	}

	Function* Transform::GetFunction(std::string name) {
		auto it = func_table_.find(name);
		assert (it != func_table_.end());
		return it->second;
	}

	void Transform::InstrumentTheInst(llvm::Instruction* target, llvm::Function* f, std::vector<llvm::Value*> &fargs) {
		IRBuilder<> builder(target);
		builder.CreateCall(f, fargs);
	}

	void Transform::visitReturnInst(const llvm::ReturnInst &return_inst) {

	}

	void Transform::visitBranchInst(const llvm::BranchInst &branch_inst) {

	}

	Constant* Transform::GetBinOpFlag(llvm::BinaryOperator* binop) {
#warning "dummy for binop flags"
		uint16_t flagvalue = 0;
		if (binop->hasNoInfs()) flagvalue = 1;
		else if (binop->hasNoNaNs()) flagvalue = 2;
		else if (binop->hasNoSignedWrap()) flagvalue = 3;
		else if (binop->hasNoSignedZeros()) flagvalue = 4;
		else if (binop->hasNoUnsignedWrap()) flagvalue = 5;
		return ConstantInt::get(i16, flagvalue, kNotsigned);
	}

	void Transform::visitBinaryOperator(BinaryOperator &binop) {
		Value *lhs = nullptr,
				*rhs = nullptr;
		if (Case(binop, &lhs, &rhs)) {
			Function *f = GetFunction(ProduceFuncName(BINOP_PREFIX, binop.getType()));
			Constant *tgt_id = BindValue(&binop),
					*lhs_id = GetValueId(lhs),
					*rhs_id = GetValueId(rhs),
					*opcode = GetOpCode(binop.getOpcode()),
					*flag = GetBinOpFlag(&binop);
			std::vector<Value*> fargs = {tgt_id, opcode, flag, lhs_id, lhs, rhs_id, rhs};
			InstrumentTheInst(&binop, f, fargs);
		}
		else
			assert (false && "not implemented");
	}

	void Transform::visitICmpInst (llvm::ICmpInst &icmp) {
		Value *lhs = nullptr, *rhs = nullptr;

		if (Case (icmp, &lhs, &rhs)) {
			Function *f = GetFunction(ProduceFuncName(ICMP_PREFIX, lhs->getType()));
			Constant *res_id = BindValue(&icmp),
					*lhs_id = GetValueId(lhs),
					*rhs_id = GetValueId(rhs),
					*cond = GetCond(icmp.getPredicate());
			std::vector<Value*> fargs = {res_id, cond, lhs_id, lhs, rhs_id, rhs};
			InstrumentTheInst(&icmp, f, fargs);
		}
		else
			assert (false && "not implemented");
	}

	void Transform::visitAllocaInst (llvm::AllocaInst &alloca) {
		ConstantInt *constant_allocator = NULL;
		Value *referenced_allocator = NULL;
		Type *allocated_type =  alloca.getAllocatedType();
		auto align = alloca.getAlignment();
		assert (allocated_type->isIntegerTy() and "sorry, only integer allocation supported yet");
		if (Case (alloca, &constant_allocator)) {
			Function *f = GetFunction(ProduceFuncName(ALLOCA_PREFIX, allocated_type));
			Constant *res_it = BindValue(&alloca);
			std::vector<Value*> fargs = {res_it, constant_allocator};
			InstrumentTheInst(&alloca, f, fargs);
		} else if (Case (alloca, &referenced_allocator)) {

		} else assert (false && "not implemented");
	}

	void Transform::visitLoadInst (llvm::LoadInst &load_inst) {

	}

	void Transform::visitStoreInst (llvm::StoreInst &store_inst) {

	}

	void Transform::visitCallInst(llvm::CallInst &call_inst) {

	}
}












