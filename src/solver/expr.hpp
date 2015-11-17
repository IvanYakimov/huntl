# ifndef __EXPR_HPP__
# define __EXPR_HPP__

// STL
# include <memory>
# include <list>
# include <string>
# include <bitset>

namespace solver
{
  class Expr : public std::enable_shared_from_this <Expr>
  {
  public:
    virtual ~Expr() = 0;
  };
  
  class Operation : public Expr
  {
	  typedef enum {
		  ADD
	  } OpCode;

	  OpCode op_code_;
	  OpCode op_code() {return op_code_;}
  };

  typedef std::shared_ptr <Expr> SharedExprPtr;

  template <size_t W> /** width (alignment) */
  class Constant : public Expr
  {
	  Constant (unsigned int value) {
		value_ = std::make_unique <std::bitset <W>> (value);
	  }
  private:
	  std::unique_ptr <std::bitset <W>> value_;
  };

  class Variable : public Expr
  {
  public:
	  Variable (std::string name) : name_(name) {}
	  std::string name() {return name_;}
  private:
	  std::string name_;
  };

  class UnaryOperation : public Operation
  {
  public:
    UnaryOperation (SharedExprPtr child) : child_ (child) {}
    SharedExprPtr child() {return child_;}
  private:
    SharedExprPtr child_;
  };

  class BinaryOperation : public Operation
  {
  public:
    BinaryOperation (SharedExprPtr left_child, SharedExprPtr right_child) :
    	left_child_(left_child), right_child_(right_child) {}
    SharedExprPtr left_child() {return left_child_;}
    SharedExprPtr right_child() {return right_child_;}
  private:
    SharedExprPtr left_child_;
    SharedExprPtr right_child_;
  };
}

# endif /* __EXPR_HPP__ */
