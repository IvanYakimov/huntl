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
#ifdef NODEF
		SharedExprPtr ProduceConstantI32 (I32 val);
		SharedExprPtr ProduceBinaryOperation (SharedExprPtr a, SharedExprPtr b, BinaryOperation::OpCode op_code);
	private:
		template <size_t W>
		SharedExprPtr ProduceConstant (unsigned int val);

#endif
	};
}

# endif /* __EXPR_FACTORY_HPP__ */
