# ifndef __BITVECTOR_EXPR_HPP__
# define __BITVECTOR_EXPR_HPP__

# include "expr.hpp"
# include "expr-factory.hpp"

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
    BitvectorNeg (SharedExprPtr a)
      : UnaryExpr (a) {}
    friend ExprFactory;
  };
    
  class BitvectorMult : public BinaryExpr
  {
  protected:
    BitvectorMult (SharedExprPtr a, SharedExprPtr b)
      : BinaryExpr (a, b) {}
    friend ExprFactory;
  };
  
  class BitvectorAdd : public BinaryExpr
  {
  protected:
    BitvectorAdd (SharedExprPtr a, SharedExprPtr b)
      : BinaryExpr (a, b) {}
    friend ExprFactory;
  };
    
  class BitvectorSub : public BinaryExpr
  {
  protected:
    BitvectorSub (SharedExprPtr a, SharedExprPtr b)
      : BinaryExpr (a, b) {}
    friend ExprFactory;
  };
}

# endif /* __BITVECTOR_EXPR_HPP__ */
