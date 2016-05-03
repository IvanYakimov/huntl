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
#include "../utils/object.hpp"
#include "kind.hpp"
#include "type.hpp"
#include "value.hpp"
#include "exception.hpp"
#include "../utils/index-cache.hpp"

namespace solver
{
	class Expr;
	class Var;
	class BinOp;
	class ObjectBuilder;
	class Const;

	/** Smart pointer to an SMT expression.
	 * \note Use ExprManager to create smart pointers to particular kinds of expressions.
	 * \see Expr
	 * \see ExprManager */
	using ExprPtr = std::shared_ptr<Expr>;

	/**
	 * A basic SMT expression.
	 * \note Every particular kind of expression should be inherited (by using CRTP <T,B>) from this.
	 * \note To create instance of particular kind of expression use ExprManager.
	 * \see Var
	 * \see Const
	 * \see BinOp
	 * \see ExprManager
	 * \see ExprPtr
	 * \see CRTP
	 */
	class Expr : public shared<Expr, Immutable> {
	public:
		virtual ~Expr() {}
	};

	/**
	 * An arbitrary binary operation. Holds (smart pointers to) left and right children, which are arbitrary smt expressions.
	 * Also holds kind of operation, which should be setup (for every instance of binary operation) in run-time.
	 * \note To create instance of binary operation use ExprManager::MkBinOp.
	 * \see ExprPtr
	 * \see Kind
	 * \see ExprManager::MkBinOp
	 */
	class BinOp : public shared<BinOp, Expr>{
	public:
		/** Basic constructor.
		 * \attention Do NOT use it directly! Use ::solver::ExprManager::MkBinOp() instead */
		BinOp(ExprPtr left_child, ExprPtr right_child, Kind kind) throw (IllegalArgException);
		~BinOp();
		/** Structural equality of this BinOp instance and another object instance. Returns true if rhs is instance of BinOp,
		 * it has equivalent kind and their left and right children are both structurally equivalent. */
		bool Equals(const Object &rhs) const final;
		/** String representation in format "(<kind> <left> <right>)", where kind - string representation of the binop's kind,
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
	 * A variable (constant in terms of SMT-LIB2). Holds variable's name and (smart pointer to) variable's type.
	 * \note To create an instance of variable use ExprManager::MkVar.
	 * \see Type
	 * \see ExprManager::MkVar
	 */
	class Var final : public shared <Var, Expr> {
	public:
		/** Basic constructor.
		 * \attention Do NOT use it directly! Use ::solver::ExprManager::MkVar() instead */
		Var (std::string name, TypePtr type) throw(IllegalArgException);
		virtual ~Var() final;
		/** Structural equality of this Var instance and another Object instance. Returns true if rhs is instance of Var
		 * and it has the same type as this.
		 */
		virtual bool Equals(const Object& rhs) const final;
		/** String representation of the variable. Returns string in format "<type> <name>",
		 * where type - string representation of a variable type and name - a name of the variable */
		virtual std::string ToString() const final;
		/** Returns name of the variable */
		std::string GetName() const;
		/** Returns (smart) pointer to a variable type */
		TypePtr GetType() const;
	private:
		std::string name_;
		TypePtr type_;
		static IndexCache<uint64_t> id_cache_;
		uint64_t id_;
	};

	/**
	 * A constant. Holds (smart pointer to) an appropriate value.
	 * \note To create an instance of constant use ExprManager::MkConst.
	 * \see Value
	 * \see ExprManager::MkConst
	 */
	class Const : public shared<Const, Expr> {
	public:
		/** Basic constructor.
		 * \attention Do NOT use it directly! Use ::solver::ExprManager::MkConst() instead */
		Const (ValuePtr val) throw(IllegalArgException);
		virtual ~Const();
		/** Structural equality of this Const instance and another Object instance. Returns true if Object is instance of Const
		 * and their values are structurally equivalent.
		 */
		virtual bool Equals(const Object& rhs) const final;
		/** String representation of the constant. Format is "<value>", where
		 * value is a string representation of the constant's value
		 */
		virtual std::string ToString() const final;
		/**
		 * Returns (smart) pointer to the stored value.
		 */
		ValuePtr GetValue() const;
	private:
		ValuePtr value_;
	};
}

# endif /* __EXPR_HPP__ */
















