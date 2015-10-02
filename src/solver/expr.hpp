# ifndef __EXPR_HPP__
# define __EXPR_HPP__

//TODO: documentation
//TODO: testing
# include <memory>
# include <list>
# include <string>

namespace solver
{
  class Expr
  {
  public:
    virtual ~Expr () = 0;
  };
  
  typedef std::shared_ptr <Expr> SharedExprPtr;

  class ConstExpr : public Expr
  {
  };

  class VariableExpr : public Expr
  {
  public:
    VariableExpr (std::string name)
    {
      name_ = name;
    }
    
    std::string name () { return name_; }
    
  private:
    std::string name_;
  };

  class UnaryExpr : public Expr
  {
  public:
    UnaryExpr (SharedExprPtr child)
    {
      child_ = child;
    }

    SharedExprPtr first () { return child_; }

  private:
    SharedExprPtr child_;
  };

  class BinaryExpr : public Expr
  {
  public:
    BinaryExpr (SharedExprPtr left_child,
		SharedExprPtr right_child)
    {
      left_child_ = left_child;
      right_child_ = right_child;
    }

    SharedExprPtr left_child	() { return left_child_; }
    SharedExprPtr right_child	() { return right_child_; }

  private:
    SharedExprPtr left_child_;
    SharedExprPtr right_child_;
  };
}

# endif /* __EXPR_HPP__ */
