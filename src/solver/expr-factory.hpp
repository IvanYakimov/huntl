# ifndef __EXPR_FACTORY_HPP__
# define __EXPR_FACTORY_HPP__

# include "expr.hpp"
# include <memory>
# include <string>

namespace solver
{
// NOTE: this factory produces only signed i32 expressions (temporary)
	class ExprFactory
	{
	public:
		template <size_t W>
		SharedExprPtr ProduceConstant (unsigned int val);
		SharedExprPtr ProduceConstantI32 (I32 val);
		SharedExprPtr ProduceVariable (std::string name);
		SharedExprPtr ProduceBinaryOperation (SharedExprPtr a, SharedExprPtr b, Operation::OpCode op_code);
	};
}

# endif /* __EXPR_FACTORY_HPP__ */
