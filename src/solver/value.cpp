# include "value.hpp"

namespace solver {
	template<typename T>
	RawInt<T>::~RawInt() {}

	template<typename T>
	RawInt<T>::RawInt(T value) : value_(value) {}

	template<typename T>
	bool RawInt<T>::Equals (const Object& rhs) const {
		auto cmp = [] (auto lhs, auto rhs) -> bool {
				return lhs.GetValue() == rhs.GetValue();
			};
		return EqualsHelper<RawInt<T>>(*this, rhs, cmp);
	}

	template<typename T>
	std::string RawInt<T>::ToString() const {
		return "i" + std::to_string(GetWidth()) + " " + std::to_string(GetValue());
	}

	template<typename T>
	T RawInt<T>::GetValue() const {
		return value_;
	}

	template<typename T>
	Width RawInt<T>::GetWidth() const {
		return sizeof(T)*8;
	}

	template<typename T>
	Alignment RawInt<T>::GetAlignment() const {
		return sizeof(T);
	}

	template<typename T>
	bool RawInt<T>::IsSigned() const {
		return std::numeric_limits<T>::is_signed;
	}
}











