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
		SharedExprPtr ProduceVariable (std::string name);
		SharedExprPtr ProduceConstantI32 (I32 val);
#ifdef NODEF
		SharedExprPtr ProduceBinaryOperation (SharedExprPtr a, SharedExprPtr b, BinaryOperation::OpCode op_code);
#endif
	private:
		template <size_t W>
		SharedExprPtr ProduceConstant (unsigned int val);
	};
}

# endif /* __EXPR_FACTORY_HPP__ */
