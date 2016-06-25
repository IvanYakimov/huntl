#ifndef __TEST_EVALUATOR_HPP__
#define __TEST_EVALUATOR_HPP__

// project
#include "../src/display.hpp"
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
	auto eval = utils::GetInstance<interpreter::Evaluator>();
	Int32Func f; {
		auto x = f.Alloca32("x");
		auto store_x = f.Store(f.I32(2), x);
		auto load_x = f.Load(x);
		auto ret = f.Ret(load_x);

		//TODO:
	}
	errs() << *f.Get() << "\n";
	eval->visit(f.Get());
}

#endif


















