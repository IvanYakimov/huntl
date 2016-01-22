# ifndef __EXPR_HPP__
# define __EXPR_HPP__

// STL
# include <memory>
# include <map>
# include <string>
# include <bitset>
# include <iostream>
# include <cstring>
// Project
# include "../utils/memory.hpp"
# include "../utils/object.hpp"

namespace solver
{
class Expr;
class Variable;
template <typename T> class Constant;
class BinaryOperation;

typedef std::shared_ptr <Expr> SharedExprPtr;
typedef std::shared_ptr <Variable> SharedVariablePtr;

  class Expr : public CRTP<Expr, Object> {
  public:
    virtual ~Expr() {}
    virtual const std::string ToString() = 0;
    virtual bool Equals (const Object& rhs) const = 0;
  };

  class Variable final : public CRTP <Variable, Expr> {
  public:
	  Variable (std::string name) : name_(name) {}
	  virtual ~Variable() final {}
	  virtual const std::string ToString() final;
	  virtual bool Equals(const Object& rhs) const final;
	  const std::string GetName() const {return name_;}
  private:
	  std::string name_;
  };

  template <typename T>
  class Constant : public CRTP<Constant<T>, Expr> {
  public:
	  Constant (T value) {value_ = value;}
	  virtual ~Constant() {}
	  virtual const std::string ToString ();
	  virtual bool Equals(const Object& rhs) const;
	  T GetValue();
  private:
	  T value_;
  };

  // ConstantI32 Instance
  template class Constant<std::int32_t>;
  class ConstantI32 final : public Constant<std::int32_t> {
	  public: ConstantI32(std::int32_t value) : Constant(value) {}
  };

  class BinaryOperation : public CRTP<BinaryOperation, Expr>{
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
		  UNSIGNED_GREATER_THAN,		// useless
		  UNSIGNED_GREATER_OR_EQUAL,	// useless
		  UNSIGNED_LESS_THAN,			// useless
		  UNSIGNED_LESS_OR_EQUAL,		// useless
		  GREATER_THAN,
		  GREATER_OR_EQUAL,
		  LESS_THAN,
		  LESS_OR_EQUAL
	};

	BinaryOperation(SharedExprPtr left_child, SharedExprPtr right_child, OpCode op_code) :
	    	op_code_(op_code), left_child_(left_child), right_child_(right_child) {}
	~BinaryOperation() {}

	SharedExprPtr GetLeftChild() {return left_child_;}
	SharedExprPtr GetRightChild() {return right_child_;}

	OpCode GetOpCode() {return op_code_;}
	std::string GetOpCodeName() {return op_code_map_[op_code_];}

    const std::string ToString() final;
    bool Equals(const Object &rhs) const;

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
			{GREATER_THAN, signed_greater_than_str},
			{GREATER_OR_EQUAL, signed_greater_or_equal_str},
			{LESS_THAN, signed_less_than_str},
			{LESS_OR_EQUAL,  signed_less_or_equal_str}
	  };
  };
}

# endif /* __EXPR_HPP__ */
