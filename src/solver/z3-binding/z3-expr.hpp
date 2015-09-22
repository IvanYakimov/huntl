// internals
# include "../iexpr.hpp"

// z3
# include <z3++.h>

// memory
# include <memory>

namespace solver
{
  class Z3Expr : public IExpr
  {
    Z3Expr (const z3::expr& expr);
    ~Z3Expr ();
    
  private:
    std::unique_ptr <z3::expr> expr_;
  };
}
