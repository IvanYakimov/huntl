# include "expr.hpp"

namespace solver
{
  class BitvectorConst : public ConstExpr
  {
  protected:
    BitvectorConst ()
      : ConstExpr () {};
    friend ExprFactory;
  };
    
  class BitvectorNeg : public UnaryExpr
  {
  protected:
    BitvectorNeg (SharedExprPtr expr)
      : UnaryExpr (expr) {}
    friend ExprFactory;
  };
  
  class BitvectorMult : public BinaryExpr
  {
  protected:
    BitvectorMult (SharedExprPtr expr)
      : BinaryExpr (expr) {}
    friend ExprFactory;
  };
  
  class BitvectorAdd : public BinaryExpr
  {
  protected:
    BitvectorMult (SharedExprPtr expr)
      : BinaryExpr (expr) {}
    friend ExprFactory;
  };
    
  class BitvectorSub : public BinaryExpr
  {
  protected:
    BitvectorSub (SharedExprPtr expr)
      : BinaryExpr (expr) {}
    friend ExprFactory;
  };
}
