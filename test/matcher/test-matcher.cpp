#include "test-matcher.hpp"

//useful link: http://llvm.org/releases/3.5.0/docs/tutorial/LangImpl3.html

using namespace llvm;


class MatcherTest : public ::testing::Test {
public:
	LLVMContext &context_ ;// = getGlobalContext();
	IRBuilder<> builder_ ;//(getGlobalContext());
	Module *module_;

	FunctionType *func_ty_;
	Function *func_;
	BasicBlock *entry_;
	interpreter::MatcherStub matcher_;
	MatcherTest() : builder_(getGlobalContext()), context_(getGlobalContext()), module_(nullptr),
			func_ty_(nullptr), func_(nullptr), entry_(nullptr){
		errs() << "constructor\n";
	}

	virtual void SetUp() {
		errs() << "setup\n";
		module_ = new Module("test", context_);
		// void func()
		func_ty_ = FunctionType::get(Type::getVoidTy(context_), false);
		func_ = Function::Create(func_ty_, Function::ExternalLinkage, "test", module_);
		entry_ = BasicBlock::Create(context_, "entry", func_);
		builder_.SetInsertPoint(entry_);
	}

	virtual void TearDown() {
		errs() << *func_ << "\n";
		ASSERT_TRUE(verifyFunction(*func_));

		for (Function::iterator i = func_->begin(), e = func_->end(); i != e; ++i) {
			matcher_.visit(i);
		}

		func_->deleteBody();

		delete module_;
		errs() << "teardown\n";
	}
};

TEST_F(MatcherTest, bodyless_function) {
}

TEST_F(MatcherTest, ret_const) {
	auto c1 = ConstantInt::get(module_->getContext(), APInt(32, 2, true));
	builder_.CreateRet(c1);
}


int main(int argc, char** argv, char **env) {
	::testing::InitGoogleTest(&argc, argv);
	return RUN_ALL_TESTS();
}











