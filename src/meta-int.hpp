#ifndef __META_INT_HPP__
#define __META_INT_HPP__

#include "llvm/ADT/APInt.h"
//#include <cvc4/cvc4.h>
#include <string>
#include <cassert>

namespace interpreter {
	using MetaInt = llvm::APInt;

	bool MetaInt_compare_(const MetaInt& lhs, const MetaInt& rhs) ;
	std::ostream& MetaInt_print_(std::ostream &os, const MetaInt& obj) ;
}

#endif













