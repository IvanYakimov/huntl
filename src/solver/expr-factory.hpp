# ifndef __EXPR_FACTORY_HPP__
# define __EXPR_FACTORY_HPP__

# include "expr.hpp"
# include <memory>
# include <string>

namespace solver
{
	class ExprFactory
	{
	public:
		SharedExprPtr ProduceVariable (std::string name);
		SharedExprPtr ProduceConstantI32 (std::int32_t val);
		SharedExprPtr ProduceBinaryOperation (SharedExprPtr a, SharedExprPtr b, BinaryOperation::OpCode op_code);
	private:
		template <typename T>
		SharedExprPtr ProduceConstant (T val);
	};
}

# endif /* __EXPR_FACTORY_HPP__ */
