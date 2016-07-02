// project
#include "../src/display.hpp"
#include "../src/meta-int.hpp"
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
#include <iostream>

using namespace memory;
using namespace interpreter;
using namespace utils;

class SymEvalTest : public ::testing::Test {
public:
	void RetChecker(ActivationRecordPtr activation, const MetaInt& expected) {
		HolderPtr actual_holder = activation->GetRet();
		HolderPtr expected_holder = Concrete::Create(expected);
		ASSERT_EQ(*expected_holder, *actual_holder);
	}
};

memory::HolderPtr DefineSymVar(solver::SolverPtr solver, solver::BitVec value) {
	auto width = value.getSize();
	auto a = solver->ExprManager().mkVar(solver->ExprManager().mkBitVectorType(width));
	auto c = solver->ExprManager().mkConst(value);
	auto a_eq_c = solver->ExprManager().mkExpr(solver::Kind::EQUAL, a, c);
	auto a_eq_c_holder = memory::Symbolic::Create(a_eq_c);
	solver->Constraint(a_eq_c_holder);
	auto a_holder = memory::Symbolic::Create(a);
	return a_holder;
}

void CheckSymRet(solver::SolverPtr solver, memory::ActivationRecordPtr act, MetaInt exp) {
	ASSERT_TRUE(solver->CheckSat());
	auto val = solver->GetValue(act->GetRet());
	auto meta_int = memory::GetValue(val);
	ASSERT_EQ(meta_int, exp);
}

void PrintSymVar(const llvm::Value* a_addr, memory::HolderPtr a_holder) {
	llvm::errs() << *a_addr << " --> ";
	std::cout << *a_holder << "\n";
}

TEST_F (SymEvalTest, assign) {
	int expected = -28;
	auto act = ActivationRecord::Create();
	auto solver = solver::Solver::Create();
	interpreter::Evaluator eval(act, solver);
	llvm::Module m("the module", llvm::getGlobalContext());
	auto a_holder = DefineSymVar(solver, solver::BitVec(32, solver::InfiniteInt(expected)));
	auto raw_func = MkIntFunc(&m, act, "f", {std::make_tuple(32, "a", a_holder)}, 32);
	auto a_addr = raw_func->arg_begin();
	PrintSymVar(a_addr, a_holder);
	Func f(raw_func); {
		auto x = f.Alloca32("x");
		auto store_x = f.Store(a_addr, x);
		auto load_x = f.Load(x);
		auto ret = f.Ret(load_x);
	}
	outs() << *f.Get() << "\n";
	eval.visit(f.Get());
	CheckSymRet(solver, act, MetaInt(32, expected));
}

TEST_F (SymEvalTest, mixed_addition) {

}




















