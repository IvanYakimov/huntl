# ifndef __BITVECTOR_EXPR_HPP__
# define __BITVECTOR_EXPR_HPP__

# include "expr.hpp"
# include "expr-factory.hpp"

namespace solver
{
  class BitvectorConst : public ConstExpr
  {
  public:
    BitvectorConst ()
      : ConstExpr () {}
  };
    
  class BitvectorNeg : public UnaryExpr
  {
  public:
    BitvectorNeg (SharedExprPtr a)
      : UnaryExpr (a) {}
  };
    
  class BitvectorMult : public BinaryExpr
  {
  public:
    BitvectorMult (SharedExprPtr a, SharedExprPtr b)
      : BinaryExpr (a, b) {}
  };
  
  class BitvectorAdd : public BinaryExpr
  {
  public:
    BitvectorAdd (SharedExprPtr a, SharedExprPtr b)
      : BinaryExpr (a, b) {}
  };
    
  class BitvectorSub : public BinaryExpr
  {
  public:
    BitvectorSub (SharedExprPtr a, SharedExprPtr b)
      : BinaryExpr (a, b) {}
  };
}

# endif /* __BITVECTOR_EXPR_HPP__ */
