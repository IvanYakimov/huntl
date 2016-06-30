// project
#include "../src/display.hpp"
#include "../src/bitvec.hpp"
#include "../src/instanceof.hpp"
#include "../src/singleton.hpp"
#include "../src/evaluator.hpp"
#include "../src/activation-record.hpp"
#include "../src/expr.hpp"
#include "../src/solver.hpp"
#include "ir-function-builder.hpp"

// gtest
#include "gtest/gtest.h"

// test
#include "llvm/IR/Verifier.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Module.h"

// std
#include <functional>

using namespace memory;
using namespace interpreter;
using namespace utils;

class EvaluatorTest : public ::testing::Test {
public:
	void RetChecker(ActivationRecordPtr activation, const BitVec& expected) {
		HolderPtr actual_holder = activation->GetRet();
		HolderPtr expected_holder = Concrete::Create(expected);
		ASSERT_EQ(*expected_holder, *actual_holder);
	}
};

TEST_F (EvaluatorTest, assign) {
	auto act = ActivationRecord::Create();
	interpreter::Evaluator eval(act);
	llvm::Module m("the module", llvm::getGlobalContext());
	solver::Solver solver;
	auto a_sym = solver.ExprManager().mkVar(solver.ExprManager().mkBitVectorType(32));
	auto a_sym_holder = memory::Symbolic::Create(a_sym);
	auto raw_func = MkIntFunc(&m, act, "f", {std::make_tuple(32, "a", a_sym_holder)}, 32);
	auto a = raw_func->arg_begin();
	Func f(raw_func); {
		auto x = f.Alloca32("x");
		auto store_x = f.Store(a, x);
		auto load_x = f.Load(x);
		auto ret = f.Ret(load_x);
	}
	outs() << *f.Get() << "\n";
	eval.visit(f.Get());
	RetChecker(act, BitVec(32,2));
}




















