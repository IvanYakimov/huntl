#ifndef __KIND_HPP__
#define __KIND_HPP__

//STL
#include <string>
#include <map>

namespace solver {
enum class Kind{
  		  /* arithmetical */
  		  ADD,
  		  SUB,
  		  MUL,
  		  DEV,
  		  REM,
  		  /* vector */
  		  SHl,
  		  LSHR,
  		  ASHR,
  		  /* logical */
  		  AND,
  		  OR,
  		  XOR,
  		  /* comparisons */
  		  EQ,
  		  NE,
  		  GT,
  		  GEQ,
  		  LT,
  		  LEQ
  	};
std::string KindToString(Kind kind);
}

#endif
