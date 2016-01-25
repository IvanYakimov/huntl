#ifndef __KIND_HPP__
#define __KIND_HPP__

//STL
#include <map>

namespace solver {
enum Kind{
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
  		  EQUAL,
  		  NOT_EQUAL,
  		  UNSIGNED_GREATER_THAN,
  		  UNSIGNED_GREATER_OR_EQUAL,
  		  UNSIGNED_LESS_THAN,
  		  UNSIGNED_LESS_OR_EQUAL,
  		  SIGNED_GREATER_THAN,
  		  SIGNED_GREATER_OR_EQUAL,
  		  SIGNED_LESS_THAN,
  		  SIGNED_LESS_OR_EQUAL
  	};

std::string KindToString(Kind kind);
}

#endif
