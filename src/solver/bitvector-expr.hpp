# ifndef __BITVECTOR_EXPR_HPP__
# define __BITVECTOR_EXPR_HPP__

//TODO: documentation
//TODO: testing

# include "expr.hpp"
# include "expr-factory.hpp"

# include <bitset>
# include <memory>

namespace solver
{
  template <size_t N> 
  class BitvectorConst : public ConstExpr
  {
  public:
    BitvectorConst (unsigned long long value)
      : ConstExpr ()
    {
      value_ = std::make_unique <std::bitset <N>> (value);
    }
  private:
    std::unique_ptr <std::bitset <N>> value_;
  };

  class BitvectorVariable : public VariableExpr
  {
  public:
    BitvectorVariable (std::string name)
      : VariableExpr (name) {}
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
