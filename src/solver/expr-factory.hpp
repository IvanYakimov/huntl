# ifndef __EXPR_FACTORY_HPP__
# define __EXPR_FACTORY_HPP__

# include "expr.hpp"
# include "bitvector-expr.hpp"

# include <memory>

namespace solver
{
  class ExprFactory
  {
    SharedExprPtr ProduceBitvectorConst ();
    SharedExprPtr ProduceBitvectorNeg (SharedExprPtr a);
    SharedExprPtr ProduceBitvectorMult (SharedExprPtr a, SharedExprPtr b);
    SharedExprPtr ProduceBitvectorAdd (SharedExprPtr a, SharedExprPtr b);
    SharedExprPtr ProduceBitvectorSub (SharedExprPtr a, SharedExprPtr b);
  };
}

# endif /* __EXPR_FACTORY_HPP__ */
