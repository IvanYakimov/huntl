# include "expr.hpp"

namespace solver
{
  class ExprFactory
  {
    SharedExprPtr ProduceBitvectorConst ();
    SharedExprPtr ProduceBitvectorNeg (SharedExprPtr a);
    SharedExprPtr ProduceBitvectorMult (SharedExprPtr a,
					SharedExprPtr b);
    SharedExprPtr ProduceBitvectorAdd (SharedExprPtr a,
				       SharedExprPtr b);
    SharedExprPtr ProduceBitvectorSub (SharedExprPtr a,
				       SharedExprPtr b);
  };
}
