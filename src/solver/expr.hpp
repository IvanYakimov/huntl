# ifndef __EXPR_HPP__
# define __EXPR_HPP__

// STL
#include <memory>
#include <map>
#include <list>
#include <string>
#include <bitset>
#include <iostream>
#include <cstring>

// Project
#include "../utils/memory.hpp"
#include "../utils/object.hpp"
#include "kind.hpp"
#include "type.hpp"
#include "value.hpp"


namespace solver
{
	class Expr;
	class Var;
	class BinOp;
	class ExprManager;

	using ExprPtr = std::shared_ptr<Expr>;
	using VarPtr = std::shared_ptr<Var>;
	using BinOpPtr = std::shared_ptr<BinOp>;

	//TODO: total refactoring
	class Expr : public CRTP<Expr, Object> {
	public:
		virtual ~Expr() {}
	};

	class BinOp : public CRTP<BinOp, Expr>{
	public:
		BinOp(ExprPtr left_child, ExprPtr right_child, Kind kind);
		~BinOp();
		std::string ToString() const final;
		bool Equals(const Object &rhs) const final;
		ExprPtr GetLeftChild() const;
		ExprPtr GetRightChild() const;
		Kind GetKind() const;
		std::string GetKindName() const;
	private:
		ExprPtr left_child_;
		ExprPtr right_child_;
		Kind kind_;
	};

	//TODO: add variable type
	class Var final : public CRTP <Var, Expr> {
	public:
		Var (std::string name, TypePtr type); //TODO: throw
		virtual ~Var() final;
		virtual std::string ToString() const final;
		virtual bool Equals(const Object& rhs) const final;
		std::string GetName() const;
		TypePtr GetType() const;
	private:
		std::string name_;
		TypePtr type_;
	};

	class Const : public CRTP<Const, Expr> {
	public:
		Const (ValuePtr val);
		virtual ~Const();
		virtual std::string ToString() const final;
		virtual bool Equals(const Object& rhs) const final;
		ValuePtr GetValue() const;
	private:
		const ValuePtr value_;
	};
	// Unsigned Integer Constant
}

# endif /* __EXPR_HPP__ */
















