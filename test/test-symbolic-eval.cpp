// project
#include "../src/meta-int.hpp"
#include "../src/instanceof.hpp"
#include "../src/singleton.hpp"
#include "../src/evaluator.hpp"
#include "../src/activation.hpp"
#include "../src/expr.hpp"
#include "../src/solver.hpp"
#include "ir-function-builder.hpp"
#include "../src/context.hpp"

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
#include "../src/local-memory.hpp"

using namespace memory;
using namespace interpreter;
using namespace utils;

class SymEvalTest : public ::testing::Test {
public:
	void RetChecker(ActivationPtr activation, interpreter::MetaIntRef expected) {
		HolderPtr actual_holder = activation->GetRet();
		HolderPtr expected_holder = Concrete::Create(expected);
		ASSERT_EQ(*expected_holder, *actual_holder);
	}

	void CheckSymRet(interpreter::ContextRef context, MetaIntRef exp) {
		ASSERT_TRUE(context.Solver().CheckSat());
		auto val = context.Solver().GetValue(context.Top()->GetRet());
		auto meta_int = memory::GetValue(val);
		ASSERT_EQ(meta_int, exp);
	}

	memory::HolderPtr DefineSymVar(interpreter::ContextRef context, solver::BitVec value) {
		auto width = value.getSize();
		auto a = context.Solver().MkVar(context.Solver().MkBitVectorType(width));
		auto c = context.Solver().MkConst(value);
		auto a_eq_c = context.Solver().MkExpr(solver::Kind::EQUAL, a, c);
		auto a_eq_c_holder = memory::Symbolic::Create(a_eq_c);
		context.Solver().Constraint(a_eq_c_holder);
		auto a_holder = memory::Symbolic::Create(a);
		return a_holder;
	}

	void PrintSymVar(const llvm::Value* a_addr, memory::HolderPtr a_holder) {
		llvm::errs() << *a_addr << " --> ";
		std::cout << *a_holder << "\n";
	}

	void Eval(ContextRef context, llvm::Function *function, ArgMapPtr arg_map, MetaIntRef exp_mint) {
		outs() << *function << "\n";
		interpreter::Evaluator eval(context);
		auto activation = memory::Activation::Create(arg_map);
		context.Push(activation);
		eval.visit(function);
		CheckSymRet(context, exp_mint);
		context.Pop();
	}
};

/// a = 2
/// ret := a
/// (ret = 2)
TEST_F (SymEvalTest, assign) {
	int expected = -28;
	interpreter::Context context;
	memory::ArgMapPtr arg_map = utils::Create<memory::ArgMap>();
	llvm::Module m("the module", llvm::getGlobalContext());
	auto a_holder = DefineSymVar(context, solver::BitVec(16, solver::InfiniteInt(expected)));
	auto raw_func = MkIntFunc(&m, "f", {std::make_tuple(16, "a")}, 16);
	auto a_addr = raw_func->arg_begin();
	arg_map->emplace(a_addr, a_holder);
	PrintSymVar(a_addr, a_holder);
	Func f(raw_func); {
		auto x = f.Alloca16("x");
		auto store_x = f.Store(a_addr, x);
		auto load_x = f.Load(x);
		auto ret = f.Ret(load_x);
	}

	Eval(context, f.Get(), arg_map, MetaInt(16, expected));
}


/// a = 2
/// ret := a + 2
/// (ret = 4)
TEST_F (SymEvalTest, mixed_addition) {
	Context context;
	auto arg_map = utils::Create<ArgMap>();
	llvm::Module m("the module", llvm::getGlobalContext());
	auto a_holder = DefineSymVar(context, solver::BitVec(16, solver::InfiniteInt(2)));
	auto raw_func = MkIntFunc(&m, "g", {std::make_tuple(16, "a")}, 16);
	auto a_addr = raw_func->arg_begin();
	arg_map->emplace(a_addr, a_holder);
	PrintSymVar(a_addr, a_holder);
	Func f(raw_func); {
		auto t1 = f.Alloca16("t1");
		f.Store(a_addr, t1);
		auto t2 = f.Load(t1);
		auto t3 = f.Add(t2, f.I16(2));
		auto ret = f.Ret(t3);
	}
	Eval(context, f.Get(), arg_map, MetaInt(16, 4));
}


















