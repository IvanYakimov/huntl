#include "test-matcher.hpp"

//useful link: http://llvm.org/releases/3.5.0/docs/tutorial/LangImpl3.html

using namespace llvm;


class MatcherTest : public ::testing::Test {
public:
	LLVMContext &context_ ;// = getGlobalContext();
	IRBuilder<> builder_ ;//(getGlobalContext());
	Module *module_;
	MatcherTest() : builder_(getGlobalContext()), context_(getGlobalContext()), module_(nullptr) {

	}
};

TEST_F(MatcherTest, bodyless_function) {
	module_ = new Module("test", context_);
	FunctionType *func_ty = FunctionType::get(Type::getVoidTy(context_), false);
	Function *func = Function::Create(func_ty, Function::ExternalLinkage, "test", module_);
	BasicBlock *entry_ = BasicBlock::Create(context_, "entry", func);
	builder_.SetInsertPoint(entry_);
	auto done = verifyFunction(*func);
	ASSERT_TRUE(done);
	errs() << *func << "\n";
	delete module_;
}

int main(int argc, char** argv, char **env) {
	::testing::InitGoogleTest(&argc, argv);
	return RUN_ALL_TESTS();
}











