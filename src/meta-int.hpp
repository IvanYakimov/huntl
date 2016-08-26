#ifndef __META_INT_HPP__
#define __META_INT_HPP__

#include "llvm/ADT/APInt.h"
//#include <cvc4/cvc4.h>
#include <string>
#include <cassert>
#include "expr.hpp"

namespace interpreter {
	using MetaInt = llvm::APInt;
	using MetaIntRef = const MetaInt&;

	bool MetaInt_compare_(const MetaInt& lhs, const MetaInt& rhs);
	std::ostream& MetaInt_print_(std::ostream &os, const MetaInt& obj);
	std::ostream& operator<<(std::ostream &os, const MetaInt& obj);

	solver::BitVec MetaInt_To_BitVec(MetaInt arg);
	MetaInt BitVec_To_MetaInt(solver::BitVec arg);

	char GetChar(MetaIntRef arg);
}

#endif













