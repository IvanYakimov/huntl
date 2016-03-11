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

	/**
	 * A basic SMT expression. Every particular kind of expression should be inherited (by using CRTP<T,B>) from this.
	 */
	class Expr : public CRTP<Expr, Object> {
	public:
		virtual ~Expr() {}
	};

	/**
	 * An arbitrary binary operation. Kind of operation is a class field and set up for every particular class instance in rut-time.
	 */
	class BinOp : public CRTP<BinOp, Expr>{
	public:
		/** Basic constructor, do NOT use it directly! Use ::solver::ExprManager::MkBinOp() instead */
		BinOp(ExprPtr left_child, ExprPtr right_child, Kind kind);
		~BinOp();
		/** Structural equality of this BinOp instance and another object instance. Returns true if rhs is instance of BinOp,
		 * it has equivalent kind and their left and right children are both structurally equivalent. */
		bool Equals(const Object &rhs) const final;
		/** String representation in format "(kind left right)", where kind - string representation of the binop's kind,
		 * left and right - string representation of the binop's children*/
		std::string ToString() const final;
		/** Returns (smart) pointer to left children */
		ExprPtr GetLeftChild() const;
		/** Returns (smart) pointer to right children */
		ExprPtr GetRightChild() const;
		/** Returns kind of the binop \see ::solver::Kind */
		Kind GetKind() const;
		/** Returns an appropriate string representation of the binop's kind */
		std::string GetKindName() const;
	private:
		ExprPtr left_child_;
		ExprPtr right_child_;
		Kind kind_;
	};

	/**
	 * A variable (constant in terms of SMT-LIB2).
	 */
	class Var final : public CRTP <Var, Expr> {
	public:
		/** Basic constructor, do NOT use it directly! Use ::solver::ExprManager::MkVar() instead */
		Var (std::string name, TypePtr type) throw(std::logic_error);
		virtual ~Var() final;
		/** Structural equality of this Var instance and another Object instance. Returns true if rhs is instance of Var
		 * and it has the same type as this.
		 */
		virtual bool Equals(const Object& rhs) const final;
		/** String representation of the variable. Returns string in format "type name",
		 * where type - string representation of a variable type and name - a name of the variable */
		virtual std::string ToString() const final;
		/** Returns name of the variable */
		std::string GetName() const;
		/** Returns (smart) pointer to a variable type */
		TypePtr GetType() const;
	private:
		std::string name_;
		TypePtr type_;
	};

	/**
	 * A constant.
	 */
	class Const : public CRTP<Const, Expr> {
	public:
		/** Basic constructor, do NOT use it directly! Use ::solver::ExprManager::MkConst() instead */
		Const (ValuePtr val) throw(std::logic_error);
		virtual ~Const();
		/** Structural equality of this Const instance and another Object instance. Returns true if Object is instance of Const
		 * and their values are structurally equivalent.
		 */
		virtual bool Equals(const Object& rhs) const final;
		/** String representation of the constant. Format is "value", where
		 * value is a string representation of the constant's value.
		 */
		virtual std::string ToString() const final;
		ValuePtr GetValue() const;
	private:
		ValuePtr value_;
	};
	// Unsigned Integer Constant
}

# endif /* __EXPR_HPP__ */
















