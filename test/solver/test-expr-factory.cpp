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
		const string name = "var_name";
		Variable var1 (name),
				var2 (name);
		ASSERT_EQ(var1, var2);
		std::shared_ptr <Expr> exp (new Variable(name));
		auto act = Factory()->ProduceVariable(name);
		ASSERT_TRUE(*exp == *act);
	}

# ifdef NODEF

	TEST_F(ExprFactoryTest, ProduceConstantI32) {
		const I32 val = 28;
		auto exp = make_shared<ConstantI32>(val);
		auto act = Factory()->ProduceConstantI32(val);
		//TODO comparison ASSERT_EQ(exp, act);
	}

	TEST_F(ExprFactoryTest, ProduceBinaryOperation) {
		auto make_var = [](std::string name) {
			return make_shared<Variable>(name);
		};

		auto x = make_var("x"),
				y = make_var("y");

		auto exp = std::make_shared<BinaryOperation> (x, y, BinaryOperation::ADD);
		auto act = Factory()->ProduceBinaryOperation(x, y, BinaryOperation::ADD);
		//TODO comparison ASSERT_EQ(exp, act);
	}
# endif
}









