#include "bitvec.hpp"

namespace solver {
	bool BitVec_compare_(const BitVec& lhs, const BitVec& rhs) {
		return lhs.eq(rhs);
	}

	std::ostream& BitVec_print_(std::ostream &os, const BitVec& obj) {
		os << obj.toString(10, obj.isSignedIntN(obj.getBitWidth()));
		return os;
	}
}
