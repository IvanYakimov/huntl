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
  		  EQUAL,
  		  NOT_EQUAL,
  		  GREATER_THAN,
  		  GREATER_OR_EQUAL,
  		  LESS_THAN,
  		  LESS_OR_EQUAL
  	};
std::string KindToString(Kind kind);
}

#endif
