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

	void Eval(llvm::Function* f, MetaInt expected) {
		outs() << *f << "\n";
		interpreter::Context context;
		interpreter::Evaluator eval(context);
		ArgMap noargs;
		auto activation = memory::Activation::Create(noargs);
		context.Push(activation);
		eval.visit(f);
		RetChecker(context, expected);
		context.Pop();
	}
};

TEST_F (EvaluatorTest, basic) {
	Int32Func f; {
		auto x = f.Alloca32("x");
		auto store_x = f.Store(f.I32(2), x);
		auto load_x = f.Load(x);
		auto ret = f.Ret(load_x);
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
			auto ret = f.Ret(load_res);
		}
	Eval(f.Get(), MetaInt(32,7));
}

/*
TEST_F(EvaluatorTest, func) {
	llvm::Module m("the module", llvm::getGlobalContext());
	memory::ArgMap arg_map;
	auto raw_func = MkIntFunc(&m, context, "func", {std::make_tuple(32, "a")}, 32);
	auto a = raw_func->arg_begin();
	arg_map.emplace(a, memory::Concrete::Create(interpreter::MetaInt(32, 2)));
	Func f(raw_func); {
		auto x = f.Alloca32("x");
		auto store_x = f.Store(a, x);
		auto load_x = f.Load(x);
		auto ret = f.Ret(load_x);
	}
	Eval(f.Get(), MetaInt(32,2), arg_map);
}
*/

#endif


















