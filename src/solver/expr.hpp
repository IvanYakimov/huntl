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
		//TODO: place Kind at first position
		BinOp(ExprPtr left_child, ExprPtr right_child, Kind kind);
		~BinOp();
		bool Equals(const Object &rhs) const final;
		std::string ToString() const final;
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
		Var (std::string name, TypePtr type) throw(std::logic_error); //TODO: throw
		virtual ~Var() final;
		virtual bool Equals(const Object& rhs) const final;
		virtual std::string ToString() const final;
		std::string GetName() const;
		TypePtr GetType() const;
	private:
		std::string name_;
		TypePtr type_;
	};

	class Const : public CRTP<Const, Expr> {
	public:
		Const (ValuePtr val) throw(std::logic_error);
		virtual ~Const();
		virtual bool Equals(const Object& rhs) const final;
		virtual std::string ToString() const final;
		ValuePtr GetValue() const;
	private:
		ValuePtr value_;
	};
	// Unsigned Integer Constant
}

# endif /* __EXPR_HPP__ */
















