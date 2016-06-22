#ifndef __BITVEC_HPP__
#define __BITVEC_HPP__

// STL
#include <memory>
#include <map>
#include <list>
#include <string>
#include <bitset>
#include <iostream>
#include <cstring>

// project
#include "expr.hpp"
#include "sort.hpp"
#include "core.hpp"
#include "../utils/index-cache.hpp"

namespace solver {
	class Var;
	//class Node;
	//class SingleNode;
	//class DoubleNode;
	//class TripleNode;
	class ObjectBuilder;
	class Const;

	template <size_t arity>
	class BitVecSort : public Sort {
		BitVecSort ();
		size_t GetArity() {return arity;}
	};

	//TODO: improve docs;

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

	enum class UnOpKind {
		BVNOT,
		BVNEG
	};

	/// BitVec -> BitVec
	class UnOp : public SingleNode<BitVec, UnOpKind, BitVecPtr, BitVecPtr> {};

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

		BinOp(BinOpKind kind, const BitVecPtr& lhs, const BitVecPtr& rhs) :
			DoubleNode <BitVec, BinOpKind, BitVecPtr, BitVecPtr, BitVecPtr> (kind, lhs, rhs)
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

	class Comparison : public DoubleNode<BitVec, ComparisonKind,
		BitVecPtr, BitVecPtr, BoolPtr> {

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
}

#endif /* __BITVEC_HPP__ */
