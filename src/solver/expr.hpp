//TODO: documentation
//TODO: testing
# include <memory>
# include <list>

namespace solver
{
  class Expr
  {
  protected:
    virtual ~Expr () = 0;
  public:
  };
  
  typedef std::shared_ptr <Expr> SharedExprPtr;

  class ConstExpr : public Expr
  {
  protected:
  };

  class UnaryExpr : public Expr
  {
  private:
    SharedExprPtr child_;
  protected:
    UnaryExpr (SharedExprPtr child)
    {
      child_ = child;
    }
  public:
    SharedExprPtr first () { return child_; }
  };

  class BinaryExpr : public Expr
  {
  private:
    SharedExprPtr left_child_;
    SharedExprPtr right_child_;
  protected:
    BinaryExpr (SharedExprPtr left_child,
		SharedExprPtr right_child)
    {
      left_child_ = left_child;
      right_child_ = right_child;
    }

    SharedExprPtr left_child	() { return left_child_; }
    SharedExprPtr right_child	() { return right_child_; }
  public:
  };
}

