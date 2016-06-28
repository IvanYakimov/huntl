#ifndef __TEST_EVALUATOR_HPP__
#define __TEST_EVALUATOR_HPP__

// project
#include "../src/display.hpp"
#include "../src/bitvec.hpp"
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
	void RetChecker(ActivationRecordPtr activation, const BitVec& expected) {
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
	eval.visit(f.Get());
	RetChecker(act, BitVec(32,2));
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

			//display->Print();
			//auto result = Object::UpCast<memory::Concrete>(display->Load(ret))->Get();
			//ASSERT_EQ(result, interpreter::BitVec(32, 7));
		}
	outs() << *f.Get() << "\n";
	eval.visit(f.Get());
	RetChecker(act, BitVec(32, 7));
}

#endif


















