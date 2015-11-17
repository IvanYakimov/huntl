# include "expr-factory.hpp"

namespace solver
{
  template <size_t W>
  SharedExprPtr ExprFactory :: ProduceConst (I32 val)
  {
	  return std::make_shared <Constant<W>>>(val);
  }

  SharedExprPtr ExprFactory :: ProduceVariable (std::string name)
  {
    return std::make_shared <Variable>(name);
  }

  SharedExprPtr ExprFactory :: ProduceUnaryOperation (SharedExprPtr a, Operation::OpCode op_code)
  {
    return std::make_shared <UnaryOperation>(a, op_code);
  }

  SharedExprPtr ExprFactory :: ProduceBinaryOperation (SharedExprPtr a, SharedExprPtr b, Operation::OpCode op_code)
  {
    return std::make_shared <BinaryOperation>(a, b, op_code);
  }
}

