#ifndef __TEST_EVALUATOR_HPP__
#define __TEST_EVALUATOR_HPP__

// project
#include "../src/meta-int.hpp"
#include "../src/instanceof.hpp"
#include "../src/singleton.hpp"
#include "../src/evaluator.hpp"
#include "../src/activation.hpp"
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
#include "../src/local-memory.hpp"
#include "../src/context.hpp"

using namespace memory;
using namespace interpreter;
using namespace utils;

class EvaluatorTest : public ::testing::Test {
public:
	void RetChecker(ContextRef c, const MetaInt& expected) {
		auto activation = c.Top();
		HolderPtr actual_holder = activation->GetRet();
		HolderPtr expected_holder = Concrete::Create(expected);
		ASSERT_EQ(*expected_holder, *actual_holder);
	}

	void Eval(llvm::Function* f, MetaInt expected, memory::ArgMapPtr args = utils::Create<memory::ArgMap>()) {
		ASSERT_FALSE(verifyFunction(*f));
		outs() << *f << "\n";
		interpreter::Context context;
		interpreter::Evaluator eval(context);
		auto activation = memory::Activation::Create(args);
		context.Push(activation);
		eval.visit(f);
		RetChecker(context, expected);
		context.Pop();
	}
};

TEST_F (EvaluatorTest, assing) {
	Int32Func f; {
		auto x = f.Alloca32("x");
		auto store_x = f.Store(f.I32(2), x);
		auto load_x = f.Load(x);
		f.Ret(load_x);
	}
	Eval(f.Get(), MetaInt(32,2));
}

TEST_F (EvaluatorTest, binop) {
	Int32Func f; {
			auto x = f.Alloca32("x");
			auto y = f.Alloca32("y");
			auto res = f.Alloca32("res");
			auto store_x = f.Store(f.I32(3), x);
			auto store_y = f.Store(f.I32(4), y);
			auto store_res = f.Store(f.I32(0), res);
			auto load_x = f.Load(x);
			auto load_y = f.Load(y);
			auto binop = f.Add(load_x, load_y);
			auto store_binop = f.Store(binop, res);
			auto load_res = f.Load(res);
			f.Ret(load_res);
		}
	Eval(f.Get(), MetaInt(32,7));
}

TEST_F(EvaluatorTest, func_with_args) {
	llvm::Module m("the module", llvm::getGlobalContext());
	memory::ArgMapPtr arg_map = utils::Create<memory::ArgMap>();
	auto raw_func = MkIntFunc(&m, "func", {std::make_tuple(16, "a")}, 16);
	auto a = raw_func->arg_begin();
	arg_map->emplace(a, memory::Concrete::Create(interpreter::MetaInt(16, 2)));
	Func f(raw_func); {
		auto x = f.Alloca16("x");
		auto store_x = f.Store(a, x);
		auto load_x = f.Load(x);
		f.Ret(load_x);
	}
	Eval(f.Get(), MetaInt(16,2), arg_map);
}

/**
int inc(int x) {
	return x + 1;
}

int f(int y) {
	return inc(y);
}
 */
TEST_F(EvaluatorTest, func_call) {
	llvm::Module m("func_call", llvm::getGlobalContext());
	memory::ArgMapPtr caller_args = utils::Create<memory::ArgMap>();
	auto caller = MkIntFunc(&m, "caller", {std::make_tuple(16, "y")}, 16);
	auto inc = MkIntFunc(&m, "inc", {std::make_tuple(16, "x")}, 16);

	auto x = inc->arg_begin();
	Func g (inc); {
		auto t1 = g.Alloca16("t1");
		auto store_x = g.Store(x, t1);
		auto t2 = g.Load(t1);
		auto t3 = g.Add(t2, g.I16(1));
		g.Ret(t3);
	}

	auto y = caller->arg_begin();
	caller_args->emplace(y, memory::Concrete::Create(interpreter::MetaInt(16, 12)));

	Func f(caller); {
		auto t1 = f.Alloca16("t1");
		auto store_y = f.Store(y, t1);
		auto t2 = f.Load(t1);
		auto t3 = f.Call(inc, t2);
		f.Ret(t3);
	}

	Eval(caller, MetaInt(16,13), caller_args);
}

#endif


















