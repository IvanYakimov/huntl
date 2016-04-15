#include "test-matcher.hpp"

//useful link: http://llvm.org/releases/3.5.0/docs/tutorial/LangImpl3.html

using namespace llvm;

//TODO: total refactoring!!!
class MatcherTest : public ::testing::Test {
public:
	LLVMContext &context_ ;// = getGlobalContext();
	IRBuilder<> builder_ ;//(getGlobalContext());
	Module *module_ = nullptr;

	Function *func_ = nullptr;
	BasicBlock *entry_ = nullptr;
	interpreter::MatcherStub matcher_;

	MatcherTest() : builder_(getGlobalContext()), context_(getGlobalContext()) {
		module_ = new Module("test", context_);
	}

	~MatcherTest() {
		delete module_;
	}

	// <-- Helpers
	AllocaInst* Alloca32(const char *name) {
		AllocaInst* res = builder_.CreateAlloca(Type::getInt32Ty(module_->getContext()), 0, name);
		res->setAlignment(4);
		return res;
	}

	ConstantInt* I32(uint32_t val) {
		return ConstantInt::get(module_->getContext(), APInt(32, val, true));
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

	BasicBlock* Block(const char* name) {
		return BasicBlock::Create(context_, name, func_);
	}

	void Enter(BasicBlock* block) {
		builder_.SetInsertPoint(block);
	}
	// -->

	//Initializators
	void InitInt32Func() {
		FunctionType *void_func_ty_ = FunctionType::get(Type::getInt32Ty(context_), false);
		func_ = Function::Create(void_func_ty_, Function::InternalLinkage, "test", module_);
	}

	void InitVoidFunc() {
		FunctionType *void_func_ty_ = FunctionType::get(Type::getVoidTy(context_), false);
		func_ = Function::Create(void_func_ty_, Function::InternalLinkage, "test", module_);
	}

	// Matching
	void MatchOnFunc() {
		errs() << *func_ << "\n";
		// If there are no errors, the function returns false.
		ASSERT_FALSE(verifyFunction(*func_));
		for (Function::iterator i = func_->begin(), e = func_->end(); i != e; ++i)
			matcher_.visit(i);
	}

	// Test confuguration
	virtual void SetUp() {
		InitInt32Func();
		entry_ = Block("entry");
		Enter(entry_);
	}

	virtual void TearDown() {
		MatchOnFunc();
	}
};

TEST_F(MatcherTest, ret__const) {
	auto ret = builder_.CreateRet(I32(42));
}

TEST_F(MatcherTest, alloca_store_load_ret) {
	auto x = Alloca32("x");
	auto store_x = Store(I32(2), x);
	auto load_x = Load(x);
	auto ret = Ret(load_x);
}

TEST_F(MatcherTest, if_than_else) {
	auto true_branch = Block("true-branch");
	auto false_branch = Block("false-branch");
	auto x = Alloca32("x");
	auto load_x = Load(x);
	auto icmp = builder_.CreateICmpEQ(load_x, I32(2));
	auto jump = builder_.CreateCondBr(icmp, true_branch, false_branch);
	Enter(true_branch);
	Ret(I32(1));
	Enter(false_branch);
	Ret(I32(-1));
}

int main(int argc, char** argv, char **env) {
	::testing::InitGoogleTest(&argc, argv);
	return RUN_ALL_TESTS();
}











