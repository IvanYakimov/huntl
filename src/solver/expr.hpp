# ifndef __EXPR_HPP__
# define __EXPR_HPP__

// STL
# include <memory>
# include <list>
# include <map>
# include <string>
# include <bitset>

namespace solver
{
typedef signed int I32;
const int kAlign_4 = 32;

  class Expr : public std::enable_shared_from_this <Expr>
  {
  public:
    virtual ~Expr() = 0;
    virtual std::string ToString() = 0;
  };
  
  typedef std::shared_ptr <Expr> SharedExprPtr;

  class Operation : public Expr
  {
  public:
	  typedef enum {
		  kAdd,
		  kSub,
		  kMul,
		  kSignDev,
		  kSignRem,
		  kShiftLeft,
		  kLogicalShiftRight,
		  kArithShiftRight,
		  kAnd,
		  kOr,
		  kXor
	  } OpCode;

	  Operation (OpCode op_code) : op_code_(op_code) {}
	  OpCode GetOpCode() {return op_code_;}

private:
	  OpCode op_code_;
	  std::map <unsigned, std::string> op_code_map_ = {
			  {kAdd, "add"},
			  {kSub, "sub"},
			  {kMul, "kMul"},
			  {kSignDev, "sdev"},
			  {kSignRem, "srem"},
			  {kShiftLeft, "shl"},
			  {kLogicalShiftRight, "lshr"},
			  {kArithShiftRight, "ashr"},
			  {kAnd, "and"},
			  {kOr, "or"},
			  {kXor, "xor"}
	  };
	  std::string GetOpCodeName() {return op_code_map_[op_code_];}
  };

  template <size_t W> /** width (alignment) */
  class Constant : public Expr
  {
	  Constant (unsigned int value) {value_ = std::make_unique <std::bitset <W>> (value);}
	  virtual std::string ToString () final;
  private:
	  std::unique_ptr <std::bitset <W>> value_;
  };

  class Variable : public Expr
  {
  public:
	  Variable (std::string name) : name_(name) {}
	  std::string ToString() final;
	  virtual ~Variable() final {}
  private:
	  std::string name_;
	  std::string GetName() {return name_;}
  };

  class UnaryOperation : public Operation
  {
  public:
    UnaryOperation (SharedExprPtr child, OpCode op_code) : Operation(op_code), child_ (child) {}
    SharedExprPtr GetChild() {return child_;}
  private:
    SharedExprPtr child_;
  };

  class BinaryOperation : public Operation
  {
  public:
    BinaryOperation (SharedExprPtr left_child, SharedExprPtr right_child, OpCode op_code) :
    	Operation(op_code), left_child_(left_child), right_child_(right_child) {}
    SharedExprPtr GetLeftChild() {return left_child_;}
    SharedExprPtr GetRightChild() {return right_child_;}
  private:
    SharedExprPtr left_child_;
    SharedExprPtr right_child_;
  };
}

# endif /* __EXPR_HPP__ */
