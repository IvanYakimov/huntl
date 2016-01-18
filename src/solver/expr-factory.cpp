# include "expr-factory.hpp"

namespace solver
{
	SharedExprPtr ExprFactory :: ProduceVariable (std::string name) {
		return std::make_shared <Variable>(name);
	}

	SharedExprPtr ExprFactory :: ProduceConstantI32 (std::int32_t val) {
		return std::make_shared <ConstantI32>(val);
	}

	template <typename T>
	SharedExprPtr ExprFactory :: ProduceConstant (T val) {
	  return std::make_shared <Constant<T>>>(val);
	}

	SharedExprPtr ExprFactory :: ProduceBinaryOperation (SharedExprPtr a, SharedExprPtr b, BinaryOperation::OpCode op_code) {
	return std::make_shared <BinaryOperation>(a, b, op_code);
	}
}

