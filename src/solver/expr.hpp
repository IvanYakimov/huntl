# ifndef __EXPR_HPP__
# define __EXPR_HPP__

#include <memory>
#include <cassert>

// Project
#include "../utils/object.hpp"

namespace solver
{
	class Expr;
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

	template <class BASE, class KIND, class X, class Y, class Z, class RES_TY>
	class TripleNode : public Node<BASE, KIND, RES_TY>  {
	public:
		NONCOPYABLE(TripleNode);

		TripleNode(KIND kind, const X& first_child, const Y& second_child, const Z& third_child)
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
}

# endif /* __EXPR_HPP__ */
















