# ifndef __EXPR_HPP__
# define __EXPR_HPP__

// STL
# include <memory>
# include <map>
# include <string>
# include <bitset>
# include <iostream>

// Project
# include "../utils/memory.hpp"

//TOOOODOOOOOOOOOOOOOOOOOOOOOOO
//TODO

namespace solver
{
//TODO redefine
typedef int32_t I32;
//TODO rename
const int kAlign_4 = 32;

class Variable;

/* Expr class implements the Barton-Nackman trick,
 * see: https://en.wikipedia.org/wiki/Barton%E2%80%93Nackman_trick
 * and: https://en.wikipedia.org/wiki/Curiously_recurring_template_pattern
 * also: http://stackoverflow.com/questions/1691007/whats-the-right-way-to-overload-operator-for-a-class-hierarchy
 * for details.
 */
  class Expr : public std::enable_shared_from_this <Expr> {
  public:
    virtual ~Expr() {}
    virtual const std::string ToString() = 0;
    virtual bool Equals (const Expr &rhs) const = 0;
    friend bool operator==(const Expr &a, const Expr &b) { return a.Equals(b); }
    friend bool operator!=(const Expr &a, const Expr &b) { return !a.Equals(b); }
  };
  
  template <typename T> class Expr_CRTP : public Expr {
  public:
	  friend bool operator==(T const &a, T const &b) { return a.Equals(b); }
	  friend bool operator!=(T const &a, T const &b) { return !a.Equals(b); }
  };

  typedef std::shared_ptr <Expr> SharedExprPtr;
  typedef std::shared_ptr <Variable> SharedVariablePtr;

  class Variable final : public Expr_CRTP <Variable> {
  public:
	  Variable (std::string name) : name_(name) {}
	  virtual ~Variable() final {}
	  virtual const std::string ToString() final;
//  protected:
	  virtual bool Equals(Expr const &rhs) const final;
  private:
	  std::string name_;
	  std::string GetName() {return name_;}
  };


  template <size_t W>
  class Constant : public Expr {
  public:
	  Constant (unsigned int value) {value_ = make_unique <std::bitset <W>> (value);}
	  virtual ~Constant() {}
	  virtual const std::string ToString ();
	  virtual bool Equals(Expr const &rhs) const;
  private:
	  //TODO re-implement without unique_ptr
	  std::unique_ptr <std::bitset <W>> value_;
  };

  // ConstantI32 Instance
  template class Constant<kAlign_4>;
  class ConstantI32 final : public Constant<kAlign_4> {
	  public: ConstantI32(I32 value) : Constant(value) {}
  };

# ifdef UNDEFINED
  class BinaryOperation : public Expr {
  public:
	enum OpCode{
		  /* arithmetical */
		  ADD,
		  SUB,
		  MUL,
		  SIGN_DEV,
		  SING_REM,
		  /* vector */
		  SHIFT_LEFT,
		  LOGICAL_SHIFT_RIGHT,
		  ARIRH_SHIFT_RIGHT,
		  /* logical */
		  AND,
		  OR,
		  XOR,
		  /* comparisons */
		  EQUAL,
		  NOT_EQUAL,
		  UNSIGNED_GREATER_THAN,
		  UNSIGNED_GREATER_OR_EQUAL,
		  UNSIGNED_LESS_THAN,
		  UNSIGNED_LESS_OR_EQUAL,
		  SIGNED_GREATER_THAN,
		  SIGNED_GREATER_OR_EQUAL,
		  SIGNED_LESS_THAN,
		  SIGNED_LESS_OR_EQUAL
	};

	BinaryOperation(SharedExprPtr left_child, SharedExprPtr right_child, OpCode op_code) :
	    	op_code_(op_code), left_child_(left_child), right_child_(right_child) {}
	~BinaryOperation() {}

	SharedExprPtr GetLeftChild() {return left_child_;}
	SharedExprPtr GetRightChild() {return right_child_;}

	OpCode GetOpCode() {return op_code_;}
	std::string GetOpCodeName() {return op_code_map_[op_code_];}

    std::string ToString() final;

  private:
    SharedExprPtr left_child_;
    SharedExprPtr right_child_;

    OpCode op_code_;

	  /* arithmetical */
	  const std::string add_str = "add";
	  const std::string sub_str = "sub";
	  const std::string mul_str = "mul";
	  const std::string sign_dev_str = "sdev";
	  const std::string sign_rem_str = "srem";

	  /* vector */
	  const std::string shift_left_str = "shl";
	  const std::string logical_shift_right_str = "lshr";
	  const std::string arith_shift_right_str = "ashr";

	  /* logical */
	  const std::string and_str = "and";
	  const std::string or_str = "or";
	  const std::string xor_str = "xor";

	  /* comparisons */
	  const std::string equal_str = "eq";
	  const std::string not_equal_str = "ne";
	  const std::string unsigned_greater_than_str = "ugt";
	  const std::string unsigned_greater_or_equal_str = "uge";
	  const std::string unsigned_less_than_str = "ult";
	  const std::string unsigned_less_or_equal_str = "ule";
	  const std::string signed_greater_than_str = "sgt";
	  const std::string signed_greater_or_equal_str = "sge";
	  const std::string signed_less_than_str = "slt";
	  const std::string signed_less_or_equal_str = "sle";

	  // TODO check map type
	std::map <OpCode, std::string> op_code_map_ = {
			/* arithmetical */
			{ADD, add_str},
			{SUB, sub_str},
			{MUL, mul_str},
			{SIGN_DEV, sign_dev_str},
			{SING_REM, sign_rem_str},

			/* vector */
			{SHIFT_LEFT, shift_left_str},
			{LOGICAL_SHIFT_RIGHT, logical_shift_right_str},
			{ARIRH_SHIFT_RIGHT, arith_shift_right_str},

			/* logical */
			{AND, and_str},
			{OR, or_str},
			{XOR, xor_str},

			/* comparisons */
			{EQUAL, equal_str},
			{NOT_EQUAL, not_equal_str},
			{UNSIGNED_GREATER_THAN, unsigned_greater_than_str},
			{UNSIGNED_GREATER_OR_EQUAL, unsigned_greater_or_equal_str},
			{UNSIGNED_LESS_THAN, unsigned_less_than_str},
			{UNSIGNED_LESS_OR_EQUAL, unsigned_less_or_equal_str},
			{SIGNED_GREATER_THAN, signed_greater_than_str},
			{SIGNED_GREATER_OR_EQUAL, signed_greater_or_equal_str},
			{SIGNED_LESS_THAN, signed_less_than_str},
			{SIGNED_LESS_OR_EQUAL,  signed_less_or_equal_str}
	  };
  };
# endif
}

# endif /* __EXPR_HPP__ */
