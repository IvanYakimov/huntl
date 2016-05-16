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
#include "exception.hpp"
#include "../utils/index-cache.hpp"

namespace solver
{
	class Expr;
	class Var;
	//class Node;
	//class SingleNode;
	//class DoubleNode;
	//class TripleNode;
	class ObjectBuilder;
	class Const;

	//TODO: improve docs;

	/** Smart pointer to an SMT expression.
	 * \note Use ObjectBuilder to create smart pointers to particular kinds of expressions.
	 * \see http://smtlib.cs.uiowa.edu/theories-FixedSizeBitVectors.shtml
	 * */
	using ExprPtr = std::shared_ptr<Expr>;

	/**
	 * A basic SMT expression.
	 * \note Every particular kind of expression should be inherited (by using CRTP <T,B>) from this.
	 * \note To create instance of particular kind of expression use ObjectBuilder.
	 */
	class Expr : public Immutable {
		//TODO: rename to BitVec!
	public:
		COMPARABLE(Expr);
		PRINTABLE(Expr);

		virtual ~Expr() {}
	};

	class BitVec : public Expr {
	public:
		virtual ~BitVec() {}
	};

	using BitVecPtr = std::shared_ptr<BitVec>;

	class Value;
	class BasicIntVal;
	template<typename T> class IntVal;

	using BasicIntPtr = std::shared_ptr<BasicIntVal>;
	template<typename T> using IntPtr = std::shared_ptr<IntVal<T>>;

	using Width = std::uint16_t;
	using Alignment = std::uint16_t;

	/** Basic integer value. This is useful to make (smart) pointer for particular integer value
	 * \see Int
	 * \see ExprManager::MkIntVal
	 */
	class BasicIntVal : public BitVec {
		using Value = uint64_t;
	public:
		virtual ~BasicIntVal();
		virtual bool Equals(const Object& rhs) const;
		virtual std::string ToString() const;
		/** Returns width (number of bits) in the integer. */
		Width GetWidth() const;
		/** Returns 64-bit unsigned long representation of the stored integer value.
		 * This routine copies significant bytes from stored raw integer value to result (in machine dependent order),
		 * and fills insignificant bytes by zeros.
		 * \see SetUInt64 */
		uint64_t GetUInt64() const;
		/** Set up value from 64-bit unsigned long representation.
		 * This routine copies significant bytes from argument to stored raw integer value (in machine dependent order),
		 * and fills insignificant bytes by zeros.
		 * For example: if we have int8_t x = "FF", the val (representing x as uint64_t) should contain "00 00 00 00 00 00 00 FF";
		 * for int32_t y = "FF FF FF FF" val = "00 00 00 00 FF FF FF FF", etc.
		 * \see GetUInt64 */
		void SetUInt64(const uint64_t& val);
	private:
		Value value_;
		Width width_;
		Alignment align_;

	};

	template <class BASE, class KIND, class RES_TY>
	class Node : public BASE {
	public:
		//NONCOPYABLE(Node);

		Node(KIND kind) : kind_(kind) {}
		virtual ~Node() {}
		KIND GetKind() const { return kind_; }
		template <class TY>
		bool HasType() const { return typeid(TY) == typeid(RES_TY); }
		bool HasSameTypeAs(const ObjectPtr &rhs) const { return instanceof<RES_TY>(rhs); };
	private:
		KIND kind_;
	};

	template<class BASE, class KIND, class X, class RES_TY>
	class SingleNode : public Node <BASE, KIND, RES_TY> {
	public:
		NONCOPYABLE(SingleNode);

		SingleNode(KIND kind, const X& child) : Node <BASE, KIND, RES_TY> (kind) {}
		~SingleNode() {}

		bool Equals(const Object& rhs) const final {
			assert(false && "not implemented");
			return false;
		}

		std::string ToString() const final {
			assert(false && "not implemented");
			return "( #unary node# )";
		}

		X GetChild() const {return child_;}
	private:
		X child_;
	};

	enum class UnOpKind {
		BVNOT,
		BVNEG
	};

	/// BitVec -> BitVec
	class UnOp : public SingleNode<BitVec, UnOpKind, BitVecPtr, BitVecPtr> {};


	/**
	 * An arbitrary binary operation. Holds (smart pointers to) left and right children, which are arbitrary smt expressions.
	 * Also holds kind of operation, which should be setup (for every instance of binary operation) in run-time.
	 * \note To create instance of binary operation use ExprManager::MkBinOp.
	 * \see ExprPtr
	 * \see Kind
	 * \see ExprManager::MkBinOp
	 */
	template <class BASE, class KIND, class X, class Y, class RES_TY>
	class DoubleNode : public Node<BASE, KIND, RES_TY> {
	public:
		//NONCOPYABLE(DoubleNode);

		/** Basic constructor.
		 * \attention Do NOT use it directly! Use ::solver::ExprManager::MkBinOp() instead */
		DoubleNode(KIND kind, const X& left_child, const Y& right_child) : Node <BASE, KIND, RES_TY> (kind) {
			left_child_ = left_child;
			right_child_ = right_child;
		}
		~DoubleNode() {}
		/** Structural equality of this BinOp instance and another object instance. Returns true if rhs is instance of BinOp,
		 * it has equivalent kind and their left and right children are both structurally equivalent. */
		bool Equals(const Object &rhs) const final {
			assert(false && "not implemented");
			return false;
		}
		/** String representation in format "(<kind> <left> <right>)", where kind - string representation of the binop's kind,
		 * left and right - string representation of the binop's children*/
		std::string ToString() const final {
			assert(false && "not implemented");
			return "( #double_node# )";
		}
		/** Returns (smart) pointer to left children */
		X GetLeftChild() const {
			return left_child_;
		}
		/** Returns (smart) pointer to right children */
		Y GetRightChild() const {
			return right_child_;
		}
	private:
		X left_child_;
		Y right_child_;
	};

	enum class BinOpKind {
		BVADD,
		BVMUL,
		BVSUB,
		BVSDIV,
		BVSREM,
		BVUDIV,
		BVUREM,
		BVSHL,
		BVLSHR,
		BVASHR,
		BVAND,
		BVOR,
		BVXOR
	};

	class BinOp : public DoubleNode<BitVec, BinOpKind, BitVecPtr, BitVecPtr, BitVecPtr> {
	public:
		//NONCOPYABLE(BinOp);

		BinOp(BinOpKind kind, const BitVecPtr& lhs, const BitVecPtr& rhs) : DoubleNode <BitVec, BinOpKind, BitVecPtr, BitVecPtr, BitVecPtr> (kind, lhs, rhs)
		{}
	};

	enum class ComparisonKind {
		BVULT,
		BVULE,
		BVUGT,
		BVUGE,
		BVSLT,
		BVSLE,
		BVSGT,
		BVSGE
	};

	class Bool {

	};

	using BoolPtr = std::shared_ptr<Bool>;

	class Comparison : public DoubleNode<BitVec, ComparisonKind,
		BitVecPtr, BitVecPtr, BoolPtr> {};

	enum class NoKind {
		EPSILON
	};

	class Equality : public DoubleNode<Expr, NoKind,
		ExprPtr, ExprPtr, BoolPtr> {};

	class Distinct : public DoubleNode<Expr, NoKind,
		ExprPtr, ExprPtr, BoolPtr> {};

	template <class BASE, class KIND, class X, class Y, class Z, class RES_TY>
	class TripleNode : public Node<BASE, KIND, RES_TY>  {
	public:
		NONCOPYABLE(TripleNode);

		TripleNode(Kind kind, const X& first_child, const Y& second_child, const Z& third_child)
			: Node<BASE, KIND, RES_TY>(kind) {}
		~TripleNode() {}
		bool Equals(const Object& rhs) const final {
			assert(false && "not implemented");
			return false;
		}

		std::string ToString() const final {
			assert(false && "not implemented");
			return "( #triple node# )";
		}
		X GetFirstChild() const { return first_; }
		Y GetSecondChild() const { return second_; }
		Z GetThirdChild() const { return third_; }
	private:
		X first_;
		Y second_;
		Z third_;
	};

	using BitVecWidth = std::uint16_t;

	/**
	 * A variable (constant in terms of SMT-LIB2). Holds variable's name and (smart pointer to) variable's type.
	 * \note To create an instance of variable use ExprManager::MkVar.
	 * \see Type
	 * \see ExprManager::MkVar
	 */
	class Var final : public BitVec {
	public:
		NONCOPYABLE(Var);

		/** Basic constructor.
		 * \attention Do NOT use it directly! Use ::solver::ExprManager::MkVar() instead */
		Var (std::string name, BitVecWidth type);
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
		BitVecWidth GetType() const;
		//TODO: move to private
		static void Reset();
	private:
		std::string name_;
		BitVecWidth type_;
		static IndexCache<uint64_t> id_cache_;
		uint64_t id_;
	};

#ifdef NODEF
	/**
	 * A constant. Holds (smart pointer to) an appropriate value.
	 * \note To create an instance of constant use ExprManager::MkConst.
	 * \see Value
	 * \see ExprManager::MkConst
	 */
	class Const : public BitVec {
	public:
		NONCOPYABLE(Const);

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
#endif
}

# endif /* __EXPR_HPP__ */
















