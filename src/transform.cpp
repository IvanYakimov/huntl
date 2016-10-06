#include "transform.hpp"

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
		//std::vector<Type*> fargs = {pstatus};
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
		InitGlobals();
		InitBinOp();
	}

	Transform::~Transform() {
	}

	Function* Transform::GetFunction(std::string name) {
		auto it = func_table_.find(name);
		assert (it != func_table_.end());
		return it->second;
	}

	// http://stackoverflow.com/questions/22310091/how-to-declare-a-function-in-llvm-and-define-it-later
	void Transform::visitBinaryOperator(BinaryOperator &binop) {
		BasicBlock *pb = binop.getParent();
		Function *f = GetFunction(BINOP_I32);
		IRBuilder<> builder(&binop);
		ConstantInt* stub = ConstantInt::get(Type::getInt32Ty(module_.getContext()), 28, false);
		std::vector<Value*> args;
		args.push_back(stub);
		//builder.CreateCall(f, args);
	}
}










