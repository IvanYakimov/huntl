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
  		  SIGN_DEV,
  		  SING_REM,
  		  /* vector */
  		  SHIFT_LEFT,
  		  LOGICAL_SHIFT_RIGHT,
  		  ARIRH_SHIFT_RIGHT,
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
