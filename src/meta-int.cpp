#include "meta-int.hpp"

namespace interpreter {
	bool MetaInt_compare_(const MetaInt& lhs, const MetaInt& rhs) {
		return lhs.eq(rhs);
	}

	std::ostream& MetaInt_print_(std::ostream &os, const MetaInt& obj) {
		os << obj.toString(10, obj.isSignedIntN(obj.getBitWidth()));
		return os;
	}

	solver::BitVec MetaInt_To_BitVec(MetaInt arg) {
		auto width = arg.getBitWidth();
		if (arg.isSignedIntN(width)) {
			int64_t tmp_sval = arg.getSExtValue();
			return solver::BitVec(width, solver::InfiniteInt(tmp_sval));
		}
		else {
			uint64_t tmp_uval = arg.getZExtValue();
			return solver::BitVec(width, solver::InfiniteInt(tmp_uval));
		}
	}

	MetaInt BitVec_To_MetaInt(solver::BitVec arg) {
		solver::InfiniteInt int_val = arg.getValue();
		uint64_t long_representation = int_val.getUnsignedLong();
		MetaInt res(arg.getSize(), long_representation);
		return res;
	}

}














