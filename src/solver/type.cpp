#include "type.hpp"

namespace solver {
	BtvType::BtvType(BTVWidth width) : width_(width) {
	}

	BTVWidth BtvType::GetBitWidth() {
		return width_;
	}

	std::size_t BtvType::GetAlignment() {
		//TODO: replace 8 by constant
		return width_ / 8;
	}

	const std::string BtvType::ToString() {
		//TODO:
		return "btv" + std::to_string(width_);
	}

	bool BtvType::Equals (const Object& rhs) const {
		auto cmp = [] (auto lhs, auto rhs) -> bool {
			return lhs.width_ == rhs.width_;
		};
		return EqualsHelper<BtvType>(*this, rhs, cmp);
	}
}











