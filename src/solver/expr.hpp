# ifndef __EXPR_HPP__
# define __EXPR_HPP__

//TODO: documentation
//TODO: testing
# include <memory>
# include <list>
# include <string>
# include <iostream>

namespace solver
{
  class Expr : public std::enable_shared_from_this <Expr>
  {
  public:
    virtual ~Expr () = 0;
    virtual std::string name () = 0;
    virtual std::ostream& operator << (std::ostream& out) = 0;
  };
  
  typedef std::shared_ptr <Expr> SharedExprPtr;

  class ConstExpr : public Expr
  {
  public:
    
    std::ostream& operator << (std::ostream& out) final;
  };

  class VariableExpr : public Expr
  {
  public:
    VariableExpr (std::string id)
    {
      id_ = id;
    }
    
    std::string id () { return id_; }

    std::ostream& operator << (std::ostream& out) final;

  private:
    std::string id_;
  };

  class UnaryExpr : public Expr
  {
  public:
    UnaryExpr (SharedExprPtr child)
    {
      child_ = child;
    }

    SharedExprPtr child () { return child_; }
    std::ostream& operator << (std::ostream& out) final;

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
    std::ostream& operator << (std::ostream& out) final;

  private:
    SharedExprPtr left_child_;
    SharedExprPtr right_child_;
  };
}

# endif /* __EXPR_HPP__ */
