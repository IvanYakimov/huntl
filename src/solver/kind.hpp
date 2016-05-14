#ifndef __KIND_HPP__
#define __KIND_HPP__

//STL
#include <map>

namespace solver {
	enum class Kind;
	/** Kind of binary operation. Most of kinds are the same as in FixedSizeBitVectors theory of SMT-LIB2 standard,
	 * but some of them are from Core theory (these are EQAUL and DISTINCT).
	 * \see to_string(Kind)
	 * \see BinOp
	 * \see http://smtlib.cs.uiowa.edu/theories.shtml
	 * \see https://en.wikipedia.org/wiki/Two%27s_complement
	 * */
	enum class Kind{
		NOT,
		NEG,
		/** Addition ('bvadd' in smt-lib2)*/
		ADD,
		/** Substruction ('bvsub' in smt-lib2)*/
		SUB,
		/** Multiplication ('bvmul' in smt-lib2)*/
		MUL,
		/** Signed division ('bvsdiv' in smt-lib2). Both args should be in two's complement format. */
		SDIV,
		/** Signed remainder ('bvsrem' in smt-lib2). Both args should be in two's complement format. */
		SREM,
		/** Unsigned division ('bvudiv' in smt-lib2). Both args represents ordinary (not two's complement) binary numbers. */
		UDIV,
		/** Unsigned reminder ('bvurem' in smt-lib2). Both args represents ordinary (not two's complenent) binary numbers.*/
		UREM,
		/** Shift left ('bvshl' in smt-lib2). */
		SHL,
		/** Logical shift right ('bvlshr' in smt-lib2). First arg represents ordinary (not two's complement) binary number. */
		LSHR,
		/** Arithmetic shift right ('bvashr' in smt-lib2). First arg should be in two's complement format. */
		ASHR,
		/** Bitwise and ('bvand' in smt-lib2). */
		AND,
		/** Bitwise of ('bvor' in smt-lib2). */
		OR,
		/** Bitwise xor ('bvxor') in smt-lib2). */
		XOR,
		/** Equality relation ('=' in smt-lib2). */
		EQUAL,
		/** Distinction relation ('distinct' in smt-lib2). */
		DISTINCT,
		/** Unsigned greater than ('ugt' in smt-lib2). Both args represents ordinary (NOT two's complenent) binary numbers. */
		UGT,
		/** Unsigned greater or equal ('uge' in smt-lib2). Both args represents ordinary (NOT two's complenent) binary numbers. */
		UGE,
		/** Unsigned less than ('ult' in smt-lib2). Both args represents ordinary (NOT two's complenent) binary numbers. */
		ULT,
		/** Unsigned less or equal ('ule' in smt-lib2). Both args represents ordinary (NOT two's complenent) binary numbers. */
		ULE,
		/** Signed greate than ('sgt' in smt-lib2). Both args should be in two's complement format. */
		SGT,
		/** Signed greater or equal ('sge' in smt-lib2). Both args should be in two's complement format. */
		SGE,
		/** Signed less than ('slt' in smt-lib2). Both args should be in two's complement format. */
		SLT,
		/** Signed less or equal ('sle' in smt-lib2). Both args should be in two's complement format. */
		SLE,
		CONCAT,
		EXTRACT,
		IF_THAN_ELSE
  	};

	/** String representation of kind.
	 * Arithmetical and logical commands has the same representation as in smt-lib2, but without bv prefix.
	 * Equality and distinction relations are represented by '=' and 'distinct'.*/
	std::string to_string(Kind kind);
}

#endif










