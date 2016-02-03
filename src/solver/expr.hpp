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
# include "type.hpp"

namespace solver
{
	class Expr;
	class Var;
	class BinOp;
	class ExprFactory;

	using SharedExpr = std::shared_ptr<Expr>;
	using SharedVar = std::shared_ptr<Var>;
	using SharedBinOp = std::shared_ptr<BinOp>;

	class ExprFactory
	{
	public:
		static SharedExpr MkVar (std::string name);
		static SharedExpr MkConstI32 (std::int32_t val);
		static SharedExpr MkBinOp (SharedExpr a, SharedExpr b, Kind op_code);
	};

	//TODO replace to helper (or tester) class
	// do not use these methods within the main program!
	//TODO rename this short-named functions
	SharedExpr C(std::int32_t val);
	SharedExpr V(std::string name);
	SharedExpr Apply(SharedExpr l, SharedExpr r, Kind k);
	SharedExpr Add(SharedExpr l, SharedExpr r);
	SharedExpr Sub(SharedExpr l, SharedExpr r);
	SharedExpr Mul(SharedExpr l, SharedExpr r);
	SharedExpr Sdiv(SharedExpr l, SharedExpr r);
	SharedExpr Srem(SharedExpr l, SharedExpr r);
	SharedExpr Udiv(SharedExpr l, SharedExpr r);
	SharedExpr Urem(SharedExpr l, SharedExpr r);
	SharedExpr Shl(SharedExpr l, SharedExpr r);
	SharedExpr Ashr(SharedExpr l, SharedExpr r);
	SharedExpr Lshr(SharedExpr l, SharedExpr r);
	SharedExpr And(SharedExpr l, SharedExpr r);
	SharedExpr Or(SharedExpr l, SharedExpr r);
	SharedExpr Xor(SharedExpr l, SharedExpr r);
	SharedExpr Eq(SharedExpr l, SharedExpr r);
	SharedExpr Ne(SharedExpr l, SharedExpr r);
	SharedExpr Sge(SharedExpr l, SharedExpr r);
	SharedExpr Sgt(SharedExpr l, SharedExpr r);
	SharedExpr Sle(SharedExpr l, SharedExpr r);
	SharedExpr Slt(SharedExpr l, SharedExpr r);
	SharedExpr Uge(SharedExpr l, SharedExpr r);
	SharedExpr Ugt(SharedExpr l, SharedExpr r);
	SharedExpr Ule(SharedExpr l, SharedExpr r);
	SharedExpr Ult(SharedExpr l, SharedExpr r);

	//TODO: total refactoring
	class Expr : public CRTP<Expr, Object> {
	public:
		virtual ~Expr() {}
		virtual const std::string ToString() = 0;
		virtual bool Equals (const Object& rhs) const = 0;
	};

	class BinOp : public CRTP<BinOp, Expr>{
	public:
		BinOp(SharedExpr left_child, SharedExpr right_child, Kind kind);
		~BinOp();
		const std::string ToString() final;
		bool Equals(const Object &rhs) const;
		SharedExpr GetLeftChild();
		SharedExpr GetRightChild();
		Kind GetKind();
		std::string GetKindName();

	private:
		SharedExpr left_child_;
		SharedExpr right_child_;
		Kind kind_;
	};

	//TODO: add variable type
	class Var final : public CRTP <Var, Expr> {
	public:
		Var (std::string name, SharedType type);
		virtual ~Var() final;
		virtual const std::string ToString() final;
		virtual bool Equals(const Object& rhs) const final;
		const std::string GetName() const;
	private:
		std::string name_;
		SharedType type_;
	};

	//TODO: add support for 8, 16, and 64-bit constants
	//TODO: extract type and value to separate class
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
















