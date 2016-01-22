#ifndef __KIND_HPP__
#define __KIND_HPP__

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
  		  UNSIGNED_GREATER_THAN,		// useless
  		  UNSIGNED_GREATER_OR_EQUAL,	// useless
  		  UNSIGNED_LESS_THAN,			// useless
  		  UNSIGNED_LESS_OR_EQUAL,		// useless
  		  GREATER_THAN,
  		  GREATER_OR_EQUAL,
  		  LESS_THAN,
  		  LESS_OR_EQUAL
  	};
}

#endif
