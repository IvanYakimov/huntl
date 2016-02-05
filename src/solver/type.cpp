#include "type.hpp"

namespace solver {
	template<typename T>
	std::string RawIntType<T>::ToString() const {
		return (IsSigned()?"i":"u") + std::to_string(GetWidth()) + " ty";
	}

	template<typename T>
	bool RawIntType<T>::Equals (const Object& rhs) const {
		auto f = [] (auto l, auto r) -> bool {return true;};
		return EqualsHelper<T>(*this, rhs, f);
	}

	template<typename T>
	Width RawIntType<T>::GetWidth() const {
		return sizeof(T)*8;
	}

	template<typename T>
	Alignment RawIntType<T>::GetAlignment() const {
		return sizeof(T);
	}

	template<typename T>
	bool RawIntType<T>::IsSigned() const {
		return std::numeric_limits<T>::is_signed;
	}
}











