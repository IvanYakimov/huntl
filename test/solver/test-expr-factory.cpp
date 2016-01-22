// Project
# include "../../src/solver/expr-factory.hpp"

// Google Test
# include "gtest/gtest.h"

// STL
# include <memory>
# include <string>
# include <iostream>

using std::shared_ptr;
using std::make_shared;
using std::string;

namespace solver {
	class ExprExprFactoryTest : public ::testing::Test {
	};

	TEST_F(ExprExprFactoryTest, ProduceVariable) {
		std::string name = "var";
		std::shared_ptr <Expr> exp (new Variable(name));
		auto act = ExprFactory::ProduceVariable(name);
		ASSERT_TRUE(*exp == *act);
	}

	TEST_F(ExprExprFactoryTest, ProduceConstantI32) {
		std::int32_t val = 28;
		std::shared_ptr<Expr> exp (new ConstantI32(val));
		auto act = ExprFactory::ProduceConstantI32(val);
		ASSERT_EQ(*exp, *act);
	}

	TEST_F(ExprExprFactoryTest, ProduceBinaryOperation) {
		auto make_var = [](std::string name) {
			return std::shared_ptr<Variable>(new Variable(name));
		};
		auto x = make_var("x"),
				y = make_var("y");
		std::shared_ptr<BinaryOperation> exp (new BinaryOperation(x, y, Kind::ADD));
		auto act = ExprFactory::ProduceBinaryOperation(x, y, Kind::ADD);
		ASSERT_EQ(*exp, *act);
	}
}









