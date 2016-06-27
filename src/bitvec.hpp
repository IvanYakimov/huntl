#ifndef __BITVEC_HPP__
#define __BITVEC_HPP__

#include "llvm/ADT/APInt.h"
//#include <cvc4/cvc4.h>
#include <string>
#include <cassert>

namespace interpreter {
	using BitVec = llvm::APInt;

	bool BitVec_compare_(const BitVec& lhs, const BitVec& rhs) ;
	std::ostream& BitVec_print_(std::ostream &os, const BitVec& obj) ;
}

#endif













