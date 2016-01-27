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
class Var;
template <typename T> class Constant;
class BinOp;
class ExprFactory;

typedef std::shared_ptr <Expr> SharedExprPtr;
typedef std::shared_ptr <Var> SharedVariablePtr;
typedef std::shared_ptr <BinOp> SharedBinaryOperationPtr;

class ExprFactory
  {
  public:
  	static SharedExprPtr MkVar (std::string name);
  	static SharedExprPtr MkConstI32 (std::int32_t val);
  	static SharedExprPtr MkBinOp (SharedExprPtr a, SharedExprPtr b, Kind op_code);
  };

SharedExprPtr C(std::int32_t val);
SharedExprPtr V(std::string name);
SharedExprPtr Apply(SharedExprPtr l, SharedExprPtr r, Kind k);
SharedExprPtr Add(SharedExprPtr l, SharedExprPtr r);
SharedExprPtr Sub(SharedExprPtr l, SharedExprPtr r);
SharedExprPtr Mul(SharedExprPtr l, SharedExprPtr r);
SharedExprPtr Sdiv(SharedExprPtr l, SharedExprPtr r);
SharedExprPtr Srem(SharedExprPtr l, SharedExprPtr r);
SharedExprPtr Udiv(SharedExprPtr l, SharedExprPtr r);
SharedExprPtr Urem(SharedExprPtr l, SharedExprPtr r);
SharedExprPtr Shl(SharedExprPtr l, SharedExprPtr r);
SharedExprPtr Ashr(SharedExprPtr l, SharedExprPtr r);
SharedExprPtr Lshr(SharedExprPtr l, SharedExprPtr r);
SharedExprPtr And(SharedExprPtr l, SharedExprPtr r);
SharedExprPtr Or(SharedExprPtr l, SharedExprPtr r);
SharedExprPtr Xor(SharedExprPtr l, SharedExprPtr r);
SharedExprPtr Eq(SharedExprPtr l, SharedExprPtr r);
SharedExprPtr Ne(SharedExprPtr l, SharedExprPtr r);
SharedExprPtr Sge(SharedExprPtr l, SharedExprPtr r);
SharedExprPtr Sgt(SharedExprPtr l, SharedExprPtr r);
SharedExprPtr Sle(SharedExprPtr l, SharedExprPtr r);
SharedExprPtr Slt(SharedExprPtr l, SharedExprPtr r);
SharedExprPtr Uge(SharedExprPtr l, SharedExprPtr r);
SharedExprPtr Ugt(SharedExprPtr l, SharedExprPtr r);
SharedExprPtr Ule(SharedExprPtr l, SharedExprPtr r);
SharedExprPtr Ult(SharedExprPtr l, SharedExprPtr r);

  class Expr : public CRTP<Expr, Object> {
  public:
    virtual ~Expr() {}
    virtual const std::string ToString() = 0;
    virtual bool Equals (const Object& rhs) const = 0;
  };

  class BinOp : public CRTP<BinOp, Expr>{
    public:
  	BinOp(SharedExprPtr left_child, SharedExprPtr right_child, Kind kind);
  	~BinOp();
  	const std::string ToString() final;
  	bool Equals(const Object &rhs) const;
  	SharedExprPtr GetLeftChild();
  	SharedExprPtr GetRightChild();
  	Kind GetKind();
  	std::string GetKindName();

    private:
      SharedExprPtr left_child_;
      SharedExprPtr right_child_;
      Kind kind_;
    };

  class Var final : public CRTP <Var, Expr> {
  public:
	  Var (std::string name);
	  virtual ~Var() final;
	  virtual const std::string ToString() final;
	  virtual bool Equals(const Object& rhs) const final;
	  const std::string GetName() const;
  private:
	  std::string name_;
  };

  class ConstI32 : public CRTP<ConstI32, Expr> {
  public:
	  ConstI32 (std::int32_t value);
	  virtual ~ConstI32();
	  virtual const std::string ToString ();
	  virtual bool Equals(const Object& rhs) const;
	  std::int32_t GetValue();
  private:
	  const std::int32_t value_;
  };

  // Unsigned Integer Constant
}

# endif /* __EXPR_HPP__ */
















