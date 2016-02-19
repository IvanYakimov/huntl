#ifndef __KIND_HPP__
#define __KIND_HPP__

//STL
#include <map>

namespace solver {
	enum class Kind;
	enum class Kind{
  		  /* arithmetical */
  		  ADD,
  		  SUB,
  		  MUL,
  		  SDIV,
  		  SREM,
		  UDIV,
		  UREM,
  		  /* vector */
  		  SHL,
  		  LSHR,
  		  ASHR,
  		  /* logical */
  		  AND,
  		  OR,
  		  XOR,
  		  /* comparisons */
  		  EQ,
  		  NE,
  		  UGT,
  		  UGE,
  		  ULT,
  		  ULE,
  		  SGT,
  		  SGE,
  		  SLT,
  		  SLE
  	};

std::string KindToString(Kind kind);
}

#endif










