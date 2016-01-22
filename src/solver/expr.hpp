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
# include "kind.hpp"

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
	  Variable (std::string name);
	  virtual ~Variable() final;
	  virtual const std::string ToString() final;
	  virtual bool Equals(const Object& rhs) const final;
	  static SharedExprPtr Create(std::string name);
	  const std::string GetName() const;
  private:
	  std::string name_;
  };

  template <typename T>
  class Constant : public CRTP<Constant<T>, Expr> {
  public:
	  Constant (T value);
	  virtual ~Constant();
	  virtual const std::string ToString ();
	  virtual bool Equals(const Object& rhs) const;
	  static SharedExprPtr Create(T value);
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
	BinaryOperation(SharedExprPtr left_child, SharedExprPtr right_child, Kind kind);
	~BinaryOperation();
	const std::string ToString() final;
	bool Equals(const Object &rhs) const;
	static SharedExprPtr Create(SharedExprPtr left_child, SharedExprPtr right_child, Kind op_code);
	SharedExprPtr GetLeftChild();
	SharedExprPtr GetRightChild();
	Kind GetOpCode();
	std::string GetOpCodeName();

  private:
    SharedExprPtr left_child_;
    SharedExprPtr right_child_;
    Kind kind_;
  };
}

# endif /* __EXPR_HPP__ */
