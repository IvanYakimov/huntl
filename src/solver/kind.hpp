#ifndef __KIND_HPP__
#define __KIND_HPP__

//STL
#include <map>

namespace solver {
	enum class Kind;
	enum class Kind{
  		  /* arithmetic */
  		  ADD,
  		  SUB,
  		  MUL,
  		  SDIV,
  		  SREM,
		  UDIV,
		  UREM,
  		  SHL,
  		  LSHR,
  		  ASHR,
  		  /* bitwise */
  		  AND,
  		  OR,
  		  XOR,
  		  /* predicates */
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










