// internals
# include "../iexpr.hpp"

// z3
# include <z3++.h>

namespace solver
{
  class Z3Expr : public IExpr
  {
    Z3Expr ();
    ~Z3Expr ();
  };
}
