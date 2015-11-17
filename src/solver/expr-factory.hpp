# ifndef __EXPR_FACTORY_HPP__
# define __EXPR_FACTORY_HPP__

# include "expr.hpp"
# include <memory>
# include <string>
#include "integer.hpp"

namespace solver
{
// TODO: re-implement by using templates
// NOTE: this factory produces only signed i32 expressions
	class ExprFactory
	{
		SharedExprPtr ProduceConst (signed int val);
		SharedExprPtr ProduceVariable (std::string name);
		SharedExprPtr ProduceUnaryOperation (SharedExprPtr a);
		SharedExprPtr ProduceBinaryOperation (SharedExprPtr a, SharedExprPtr b);
	};
}

# endif /* __EXPR_FACTORY_HPP__ */
