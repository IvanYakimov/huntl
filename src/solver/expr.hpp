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

class ExprFactory;

typedef std::shared_ptr <Expr> SharedExprPtr;
typedef std::shared_ptr <Variable> SharedVariablePtr;
typedef std::shared_ptr <BinaryOperation> SharedBinaryOperationPtr;

class ExprFactory
  {
  public:
  	static SharedExprPtr ProduceVariable (std::string name);
  	static SharedExprPtr ProduceConstantI32 (std::int32_t val);
  	static SharedExprPtr ProduceBinaryOperation (SharedExprPtr a, SharedExprPtr b, Kind op_code);
  };

  class Expr : public CRTP<Expr, Object> {
  public:
    virtual ~Expr() {}
    virtual const std::string ToString() = 0;
    virtual bool Equals (const Object& rhs) const = 0;
    //TODO: refactoring
    friend SharedExprPtr eq(SharedExprPtr l, SharedExprPtr r);
    friend SharedExprPtr eq(SharedExprPtr l, std::int32_t r);
    friend SharedExprPtr eq(std::int32_t l, SharedExprPtr r);
    friend SharedExprPtr slt(SharedExprPtr l, SharedExprPtr r);
    friend SharedExprPtr slt(SharedExprPtr l, std::int32_t r);
    friend SharedExprPtr slt(std::int32_t l, SharedExprPtr r);
  };

  class BinaryOperation : public CRTP<BinaryOperation, Expr>{
    public:
  	BinaryOperation(SharedExprPtr left_child, SharedExprPtr right_child, Kind kind);
  	~BinaryOperation();
  	const std::string ToString() final;
  	bool Equals(const Object &rhs) const;
  	SharedExprPtr GetLeftChild();
  	SharedExprPtr GetRightChild();
  	Kind GetOpCode();
  	std::string GetOpCodeName();

    private:
      SharedExprPtr left_child_;
      SharedExprPtr right_child_;
      Kind kind_;
    };

  class Variable final : public CRTP <Variable, Expr> {
  public:
	  Variable (std::string name);
	  virtual ~Variable() final;
	  virtual const std::string ToString() final;
	  virtual bool Equals(const Object& rhs) const final;
	  const std::string GetName() const;
  private:
	  std::string name_;
  };

  class ConstantI32 : public CRTP<ConstantI32, Expr> {
  public:
	  ConstantI32 (std::int32_t value);
	  virtual ~ConstantI32();
	  virtual const std::string ToString ();
	  virtual bool Equals(const Object& rhs) const;
	  std::int32_t GetValue();
  private:
	  const std::int32_t value_;
  };

  // Unsigned Integer Constant
}

# endif /* __EXPR_HPP__ */
















