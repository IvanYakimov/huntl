#include "type.hpp"

namespace solver {
		RawIntType::~RawIntType() {}
		RawIntType::RawIntType ();
		const std::string RawIntType::ToString() final;
		bool RawIntType::Equals (const Object& rhs) final;
		unsigned int RawIntType::Width() final;
		std::size_t RawIntType::Alignment() final;
		bool RawIntType::IsSigned() final;
}











