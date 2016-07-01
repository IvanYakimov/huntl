#include "meta-int.hpp"

namespace interpreter {
	bool MetaInt_compare_(const MetaInt& lhs, const MetaInt& rhs) {
		return lhs.eq(rhs);
	}

	std::ostream& MetaInt_print_(std::ostream &os, const MetaInt& obj) {
		os << obj.toString(10, obj.isSignedIntN(obj.getBitWidth()));
		return os;
	}
}
