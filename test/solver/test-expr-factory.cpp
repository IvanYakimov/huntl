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
	class ExprFactoryTest : public ::testing::Test {
	public:
		void SetUp() { factory_ = new ExprFactory(); }
		void TearDown() { delete factory_; }
		ExprFactory *Factory() { return factory_ ; }
	private:
		ExprFactory *factory_ = nullptr;
	};

	TEST_F(ExprFactoryTest, ProduceVariable) {
		std::string name = "var";
		std::shared_ptr <Expr> exp (new Variable(name));
		auto act = Factory()->ProduceVariable(name);
		ASSERT_TRUE(*exp == *act);
	}

	TEST_F(ExprFactoryTest, ProduceConstantI32) {
		std::int32_t val = 28;
		std::shared_ptr<Expr> exp (new ConstantI32(val));
		auto act = Factory()->ProduceConstantI32(val);
		ASSERT_EQ(*exp, *act);
	}

	TEST_F(ExprFactoryTest, ProduceBinaryOperation) {
		auto make_var = [](std::string name) {
			return std::shared_ptr<Variable>(new Variable(name));
		};
		auto x = make_var("x"),
				y = make_var("y");
		std::shared_ptr<BinaryOperation> exp (new BinaryOperation(x, y, BinaryOperation::ADD));
		auto act = Factory()->ProduceBinaryOperation(x, y, BinaryOperation::ADD);
		ASSERT_EQ(*exp, *act);
	}
}









