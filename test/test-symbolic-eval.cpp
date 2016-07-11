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
	void RetChecker(memory::HolderPtr ret, const MetaInt& expected) {
		HolderPtr expected_holder = Concrete::Create(expected);
		ASSERT_EQ(*ret, *expected_holder);
	}

	void CheckSymRet(ContextRef context, memory::HolderPtr ret_holder, MetaIntRef exp) {
		ASSERT_TRUE(context.Solver().CheckSat());
		ASSERT_TRUE(memory::IsSymbolic(ret_holder));
		auto ret_expr = memory::GetExpr(ret_holder);
		auto meta_int = context.Solver().GetValue(ret_expr);
		ASSERT_EQ(meta_int, exp);
	}

	memory::HolderPtr DefineSymVar(interpreter::ContextRef context, solver::BitVec value) {
		auto width = value.getSize();
		auto a = context.Solver().MkVar(context.Solver().MkBitVectorType(width));
		auto c = context.Solver().MkConst(value);
		auto a_eq_c = context.Solver().MkExpr(solver::Kind::EQUAL, a, c);
		context.Solver().Constraint(a_eq_c);
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
		auto activation = memory::Activation::Create();
		context.Push();
		auto ret = eval.Do(function, arg_map);
		CheckSymRet(context, ret, exp_mint);
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

TEST_F (SymEvalTest, mksym_uiN) {
	interpreter::Context c;
	llvm::Module m("the module", llvm::getGlobalContext());
	auto mksym_16 = MkIntFunc(&m, "mksym_i16", {}, 16);
	interpreter::Evaluator eval(c);
	memory::ArgMapPtr caller_args = utils::Create<memory::ArgMap>();

	auto caller = MkIntFunc(&m, "caller", {}, 16);

	Func f(caller); {
		auto x = f.Alloca16("x");
		auto t1 = f.Call(mksym_16);
		f.Store(t1, x);
		auto t2 = f.Load(x);
		auto t3 = f.Add(t2, f.I16(2));
		f.Store(t3, x);
		auto t4 = f.Load(x);
		f.Ret(t4);
	}

	eval.Do(&m);
	//Eval(c, caller, caller_args, MetaInt(16,4));
	auto ret_holder = eval.Do(caller, caller_args);
	ASSERT_TRUE(c.Solver().CheckSat());
}
















