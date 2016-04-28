#include "test-executor.hpp"

using namespace interpreter;

class ExecutorTest : public ::testing::Test {
public:
	const StateId owner_ = 2;
	DisplayPtr disp_;
	Executor *exec_ = nullptr;

	ExecutorTest() {
		disp_ = std::make_shared<DisplayStub>(Memory::Get(), owner_);
		exec_ = new Executor(disp_);
	}

	~ExecutorTest() {
		delete exec_;
	}

	// TODO: visit only one basic-block!
	void Exec(Func &func) {
		Function* f = func.Get();
		errs() << *f << "\n";
		ASSERT_FALSE(verifyFunction(*f));
		// If there are no errors, the function returns false.

		for (Function::iterator i = f->begin(), e = f->end(); i != e; ++i)
			exec_->visit(i);
	}
};

TEST_F(ExecutorTest, ret__const32) {
	Int32Func f; {
		auto ret = f.Ret(f.I32(42));
	}
	Exec(f);
}

TEST_F(ExecutorTest, basic_allocation) {

}
