#ifndef __TEST_EVALUATOR_HPP__
#define __TEST_EVALUATOR_HPP__

// project
#include "../src/display.hpp"
#include "../src/bitvec.hpp"
#include "../src/instanceof.hpp"
#include "../src/singleton.hpp"
#include "../src/evaluator.hpp"
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
using namespace utils;

class EvaluatorTest : public ::testing::Test {
public:
};

TEST_F (EvaluatorTest, basic) {
	interpreter::Evaluator eval;
	Int32Func f; {
		auto x = f.Alloca32("x");
		auto store_x = f.Store(f.I32(2), x);
		auto load_x = f.Load(x);
		auto ret = f.Ret(load_x);

		//TODO:
	}
	errs() << *f.Get() << "\n";
	eval.visit(f.Get());
}

TEST_F (EvaluatorTest, binop) {
	interpreter::Evaluator eval;
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
	errs() << *f.Get() << "\n";
	eval.visit(f.Get());
}

#endif


















