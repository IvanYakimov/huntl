# include "expr-factory.hpp"

namespace solver
{
  template <size_t N>
  SharedExprPtr ExprFactory :: ProduceBitvectorConst (unsigned long long val)
  {
    return std::make_shared <BitvectorConst<N>> (val);
  }

  SharedExprPtr ExprFactory :: ProduceBitvectorVariable (std::string name)
  {
    return std::make_shared <BitvectorVariable> (name);
  }

  SharedExprPtr ExprFactory :: ProduceBitvectorNeg (SharedExprPtr a)
  {
    return std::make_shared <BitvectorNeg> (a);
  }

  SharedExprPtr ExprFactory :: ProduceBitvectorMult (SharedExprPtr a, SharedExprPtr b)
  {
    return std::make_shared <BitvectorMult> (a, b);
  }

  SharedExprPtr ExprFactory :: ProduceBitvectorAdd (SharedExprPtr a, SharedExprPtr b)
  {
    return std::make_shared <BitvectorAdd> (a, b);
  }

  SharedExprPtr ExprFactory :: ProduceBitvectorSub (SharedExprPtr a, SharedExprPtr b)
  {
    return std::make_shared <BitvectorSub> (a, b);
  }
}
