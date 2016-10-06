#include "transform.hpp"

#include "case.hpp"

namespace transform {
	using namespace llvm;

	void Transform::DeclareFunction(std::string name, FunctionType* ftype) {
		Function* f = Function::Create(ftype, Function::ExternalLinkage, name.c_str(), &module_);
		func_table_.emplace(name, f);
	}

	void Transform::InitGlobals() {
		Type* i8ptr = PointerType::get(i8, 0);
		Type* i8ptr_ptr = PointerType::get(i8ptr, 0);
		status_ = new GlobalVariable(module_, i8, false, GlobalVariable::ExternalLinkage, 0, "status");
		status_->setAlignment(1);
		status_ptr_ = new GlobalVariable(module_, i8ptr, false, GlobalVariable::ExternalLinkage, 0, "status_ptr");
		status_ptr_->setAlignment(8);
		ConstantInt* status_const = ConstantInt::get(module_.getContext(), APInt(8, 0L));
		status_->setInitializer(status_const);
		status_ptr_->setInitializer(status_);
		errs() << "status: \n" << *status_ << "\n";
	}

	void Transform::InitBinOp() {
		auto opcode = i32;
		auto ref = i64;
		auto flag = i16;
		auto val = i32;
		auto pstatus = PointerType::get(PointerType::get(i8,0),0);
		std::vector<Type*> fargs = {ref, opcode, flag, ref, val, ref, val};
		FunctionType* ftype = FunctionType::get(val, fargs, false);
		std::string fname(BINOP_I32);
		DeclareFunction(fname, ftype);
	}

	void Transform::InitTypes() {
		LLVMContext& context = module_.getContext();
		i1 = Type::getInt1Ty(context);
		i8 = Type::getInt8Ty(context);
		i16 = Type::getInt16Ty(context);
		i32 = Type::getInt32Ty(context);
		i64 = Type::getInt64Ty(context);
	}

	Transform::Transform(Module& module) : module_(module) {
		InitTypes();
		//InitGlobals();
		InitBinOp();
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

	// this is a common template
	Constant* Transform::GetValueId(Value* val) {
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
			Function *transformer = GetFunction(BINOP_I32);
			Constant *tgt_id = BindValue(&binop),
					*lhs_id = GetValueId(lhs),
					*rhs_id = GetValueId(rhs),
					*opcode = GetOpCode(binop.getOpcode()),
					*flag = GetBinOpFlag(&binop);
			std::vector<Value*> args = {tgt_id, opcode, flag, lhs_id, lhs, rhs_id, rhs};
			InstrumentTheInst(&binop, transformer, args);
		}
		else
			assert (false && "not implemented");
	}

	void Transform::visitICmpInst (llvm::ICmpInst &icmp) {
		Value *lhs = nullptr, *rhs = nullptr;

		if (Case (icmp, &lhs, &rhs)) {

			//Function *f = GetFunction("");
		}
		else
			assert (false && "not implemented");
	}

	void Transform::visitAllocaInst (const llvm::AllocaInst &alloca_inst) {

	}

	void Transform::visitLoadInst (const llvm::LoadInst &load_inst) {

	}

	void Transform::visitStoreInst (const llvm::StoreInst &store_inst) {

	}

	void Transform::visitCallInst(const llvm::CallInst &call_inst) {

	}
}












