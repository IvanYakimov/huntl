#include "test-matcher.hpp"

//useful link: http://llvm.org/releases/3.5.0/docs/tutorial/LangImpl3.html

using namespace llvm;

class Func {
protected:
	LLVMContext &context_ ;// = getGlobalContext();
	IRBuilder<> builder_ ;//(getGlobalContext());
	Module* module_ = nullptr;
	FunctionType* func_ty_ = nullptr;
	Function* func_ = nullptr;
	BasicBlock* entry_ = nullptr;

public:
	Func(FunctionType* ty, const char* name) : builder_(getGlobalContext()), context_(getGlobalContext()) {
		module_ = new Module("test", context_);
		func_= Function::Create(ty, Function::InternalLinkage, name, module_);
		entry_ = Block("entry");
		Enter(entry_);
	}

	virtual ~Func() {
		delete module_;
	}

	Function* Get() {
		return func_;
	}

	BasicBlock* Entry() {
		return entry_;
	}

	BasicBlock* Block(const char* name) {
		return BasicBlock::Create(context_, name, func_);
	}

	void Enter(BasicBlock* block) {
		builder_.SetInsertPoint(block);
	}


	AllocaInst* Alloca32(const char *name) {
		AllocaInst* res = builder_.CreateAlloca(Type::getInt32Ty(context_), 0, name);
		res->setAlignment(4);
		return res;
	}

	ConstantInt* I32(uint32_t val) {
		return ConstantInt::get(context_, APInt(32, val, true));
	}

	ConstantInt* I1(bool val) {
		if (val == true)
			return ConstantInt::get(context_, APInt(1, 1, true));
		else
			return ConstantInt::get(context_, APInt(1, 0, true));
	}

	ConstantInt* True() {
		return I1(true);
	}

	ConstantInt* False() {
		return I1(false);
	}

	StoreInst* Store(Value* what, Value* where) {
		return builder_.CreateStore(what, where);
	}

	LoadInst* Load(Value *from) {
		return builder_.CreateLoad(from);
	}

	ReturnInst* Ret(Value *what) {
		return builder_.CreateRet(what);
	}

	ReturnInst* RetVoid() {
		return builder_.CreateRetVoid();
	}

	Value* EQ(Value* lhs, Value* rhs) {
		return builder_.CreateICmpEQ(lhs, rhs);
	}

	Value* NE(Value* lhs, Value* rhs) {
		return builder_.CreateICmpNE(lhs, rhs);
	}

	BranchInst* IfThanElse(Value* cond, BasicBlock* iftrue, BasicBlock* iffalse) {
		return builder_.CreateCondBr(cond, iftrue, iffalse);
	}

	BranchInst* Jump(BasicBlock* dest) {
		return builder_.CreateBr(dest);
	}

	Value* Add(Value* lhs, Value* rhs) {
		return builder_.CreateAdd(lhs, rhs);
	}

	//TODO: Make variadic
	PHINode* Phi(Type* ty) {
		return builder_.CreatePHI(ty, 0);
	}

	Value* ZExt(Value* val, Type* ty){
		return builder_.CreateZExt(val, ty);
	}

	Type* Int32Ty() {
		return Type::getInt32Ty(context_);
	}

	Type* Int1Ty() {
		return Type::getInt1Ty(context_);
	}

	Type* VoidTy() {
		return Type::getVoidTy(context_);
	}
};

class Int32Func : public Func {
public:
	Int32Func(const char* name = "f") : Func(FunctionType::get(Type::getInt32Ty(getGlobalContext()), false), name) {}
};

class VoidFunc : public Func {
public:
	VoidFunc(const char* name = "f") : Func(FunctionType::get(Type::getVoidTy(getGlobalContext()), false), name) {}
};

//TODO: total refactoring!!!
class MatcherTest : public ::testing::Test {
public:
	interpreter::MatcherStub matcher_;

	// Matching
	void Match(Func &func) {
		Function* f = func.Get();
		errs() << *f << "\n";
		ASSERT_FALSE(verifyFunction(*f));
		// If there are no errors, the function returns false.

		for (Function::iterator i = f->begin(), e = f->end(); i != e; ++i)
			matcher_.visit(i);
	}
};

TEST_F(MatcherTest, ret__void) {
	VoidFunc f; {
		auto ret = f.RetVoid();
	}
	Match(f);
}

TEST_F(MatcherTest, ret__const) {
	Int32Func f; {
		auto ret = f.Ret(f.I32(42));
	}
	Match(f);
}

TEST_F(MatcherTest, alloca_store_load_ret) {
	Int32Func f; {
		auto x = f.Alloca32("x");
		auto store_x = f.Store(f.I32(2), x);
		auto load_x = f.Load(x);
		auto ret = f.Ret(load_x);
	}
	Match(f);
}

TEST_F(MatcherTest, if_than_else) {
	Int32Func f; {
		auto true_branch = f.Block("true-branch");
		auto false_branch = f.Block("false-branch");
		auto x = f.Alloca32("x");
		auto icmp = f.EQ(f.Load(x), f.I32(2));
		auto jump = f.IfThanElse(icmp, true_branch, false_branch);
		f.Enter(true_branch); {
			auto ret = f.Ret(f.I32(1));
		}
		f.Enter(false_branch); {
			auto ret = f.Ret(f.I32(-1));
		}
	}
	Match(f);
}

TEST_F(MatcherTest, jump) {
	Int32Func f; {
		auto dest = f.Block("dest");
		auto jump = f.Jump(dest);
		f.Enter(dest); {
			f.Ret(f.I32(0));
		}
	}
	Match(f);
}

TEST_F(MatcherTest, binop) {
	Int32Func f; {
		auto x = f.Alloca32("x");
		auto y = f.Alloca32("y");
		auto binop = f.Add(f.Load(x), f.Load(y));
		auto ret = f.Ret(binop);
	}
	Match(f);
}

TEST_F(MatcherTest, phi_node) {
	Int32Func f; {
		auto more_cmp = f.Block("more_cmp");
		auto phi_node = f.Block("phi_node");
		auto x = f.Alloca32("x");
		auto y = f.Alloca32("y");
		auto cmp_x = f.NE(f.Load(x), f.I32(0));
		auto br1 = f.IfThanElse(cmp_x, phi_node, more_cmp);
		Value* cmp_y;
		f.Enter(more_cmp); {
			cmp_y = f.NE(f.Load(y), f.I32(0));
			auto br2 = f.Jump(phi_node);
		}
		f.Enter(phi_node); {
			PHINode* phi = f.Phi(f.Int1Ty());
			phi->addIncoming(f.I1(true), f.Entry());
			phi->addIncoming(cmp_y, more_cmp);
			auto zext = f.ZExt(phi, f.Int32Ty());
			auto ret = f.Ret(zext);
		}
	}
	Match(f);
}

int main(int argc, char** argv, char **env) {
	::testing::InitGoogleTest(&argc, argv);
	return RUN_ALL_TESTS();
}











