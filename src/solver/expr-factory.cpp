# include "expr-factory.hpp"

namespace solver
{
  template <size_t W>
  SharedExprPtr ExprFactory :: ProduceConstant (unsigned int val) {
	  return std::make_shared <Constant<W>>>(val);
  }

  SharedExprPtr ExprFactory :: ProduceConstantI32 (I32 val) {
	  return std::make_shared <ConstantI32>(val);
  }

  SharedExprPtr ExprFactory :: ProduceVariable (std::string name) {
    return std::make_shared <Variable>(name);
  }

  SharedExprPtr ExprFactory :: ProduceBinaryOperation (SharedExprPtr a, SharedExprPtr b, Operation::OpCode op_code) {
    return std::make_shared <BinaryOperation>(a, b, op_code);
  }
}

