#ifndef __TEST_EVALUATOR_HPP__
#define __TEST_EVALUATOR_HPP__

// project
#include "../src/display.hpp"
#include "../src/meta-int.hpp"
#include "../src/instanceof.hpp"
#include "../src/singleton.hpp"
#include "../src/evaluator.hpp"
#include "../src/activation-record.hpp"
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
	void RetChecker(ActivationRecordPtr activation, const MetaInt& expected) {
		HolderPtr actual_holder = activation->GetRet();
		HolderPtr expected_holder = Concrete::Create(expected);
		ASSERT_EQ(*expected_holder, *actual_holder);
	}
};

TEST_F (EvaluatorTest, basic) {
	auto act = ActivationRecord::Create();
	interpreter::Evaluator eval(act);
	Int32Func f; {
		auto x = f.Alloca32("x");
		auto store_x = f.Store(f.I32(2), x);
		auto load_x = f.Load(x);
		auto ret = f.Ret(load_x);
	}
	outs() << *f.Get() << "\n";
	eval.Do(f.Get(), act);
	RetChecker(act, MetaInt(32,2));
}

TEST_F (EvaluatorTest, binop) {
	auto act = ActivationRecord::Create();
	interpreter::Evaluator eval(act);
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
	outs() << *f.Get() << "\n";
	eval.Do(f.Get(), act);
	RetChecker(act, MetaInt(32, 7));
}

TEST_F(EvaluatorTest, funcPwith_args) {
	auto act = ActivationRecord::Create();
	interpreter::Evaluator eval(act);
	llvm::Module m("the module", llvm::getGlobalContext());
	std::vector<Type*>f_args;
	f_args.push_back(IntegerType::get(m.getContext(), 8));
	llvm::FunctionType* f_type = llvm::FunctionType::get(
			IntegerType::get(m.getContext(), 32),
			f_args,
			false
			);
	auto raw_func = llvm::Function::Create(f_type, Function::InternalLinkage, "func", &m);
	llvm::Function::arg_iterator args = raw_func->arg_begin();
	llvm::Value* a = args++;
	a->setName("a");
	act->SetArg(a, Concrete::Create(MetaInt(32, 2)));
	Func f(raw_func); {
		auto x = f.Alloca32("x");
		auto store_x = f.Store(a, x);
		auto load_x = f.Load(x);
		auto ret = f.Ret(load_x);
	}
	outs() << *f.Get() << "\n";
	eval.Do(f.Get(), act);
	RetChecker(act, MetaInt(32,2));
}

TEST_F(EvaluatorTest, func) {
	auto act = ActivationRecord::Create();
	interpreter::Evaluator eval(act);
	llvm::Module m("the module", llvm::getGlobalContext());
	auto raw_func = MkIntFunc(&m, act, "func", {std::make_tuple(32, "a", memory::Concrete::Create(MetaInt(32,2)))}, 32);
	auto a = raw_func->arg_begin();
	Func f(raw_func); {
		auto x = f.Alloca32("x");
		auto store_x = f.Store(a, x);
		auto load_x = f.Load(x);
		auto ret = f.Ret(load_x);
	}
	outs() << *f.Get() << "\n";
	eval.Do(&m);
	RetChecker(act, MetaInt(32,2));
}

#endif


















