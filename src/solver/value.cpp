# include "value.hpp"

namespace solver {
	template<typename T>
	Int<T>::~Int() {}

	template<typename T>
	Int<T>::Int(T value) : value_(value) {}


	template<typename T>
	bool Int<T>::Equals (const Object& rhs) const {
		auto cmp = [] (auto lhs, auto rhs) -> bool {
				return lhs.GetValue() == rhs.GetValue();
			};
		return EqualsHelper<Int<T>>(*this, rhs, cmp);
	}

	template<typename T>
	std::string Int<T>::ToString() const {
		return (IsSigned()?"i":"u") + std::to_string(GetWidth()) + " " + std::to_string(GetValue());
	}

	template<typename T>
	T Int<T>::GetValue() const {
		return value_;
	}

	template<typename T>
	Width Int<T>::GetWidth() const {
		return sizeof(T)*8;
	}

	template<typename T>
	Alignment Int<T>::GetAlignment() const {
		return sizeof(T);
	}

	template<typename T>
	bool Int<T>::IsSigned() const {
		return std::numeric_limits<T>::is_signed;
	}
}











