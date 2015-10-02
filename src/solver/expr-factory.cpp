# include "expr-factory.hpp"

namespace solver
{
  SharedExprPtr ExprFactory :: ProduceBitvectorConst ()
  {
    return std::make_shared <BitvectorConst> ();
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
