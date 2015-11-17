# include "expr-factory.hpp"

namespace solver
{
  template <size_t W>
  SharedExprPtr ExprFactory :: ProduceConst (signed int val)
  {
    return std::make_shared <IntegerConst<W>>>(val);
  }

  SharedExprPtr ExprFactory :: ProduceVariable (std::string name)
  {
    return std::make_shared <Variable>(name);
  }

  SharedExprPtr ExprFactory :: ProduceUnaryOperation (SharedExprPtr a)
  {
    return std::make_shared <UnaryOperation>(a);
  }

  SharedExprPtr ExprFactory :: ProduceBinaryOperation (SharedExprPtr a, SharedExprPtr b)
  {
    return std::make_shared <BinaryOperation>(a, b);
  }
}
